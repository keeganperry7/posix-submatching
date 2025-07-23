import PosixSubmatching.Regex

open Regex

universe u

variable {α : Type u}

inductive POSIX : Regex α → List α → List (String × List α) → Prop
  | epsilon : POSIX epsilon [] []
  | char (c : α) : POSIX (char c) [c] []
  | left {r₁ r₂ : Regex α} {s : List α} {Γ : List (String × List α)} :
    POSIX r₁ s Γ →
    POSIX (plus r₁ r₂) s Γ
  | right {r₁ r₂ : Regex α} {s : List α} {Γ : List (String × List α)} :
    POSIX r₂ s Γ →
    ¬r₁.Matches s →
    POSIX (plus r₁ r₂) s Γ
  | mul {r₁ r₂ : Regex α} {s₁ s₂ : List α} {Γ₁ Γ₂ : List (String × List α)} :
    POSIX r₁ s₁ Γ₁ →
    POSIX r₂ s₂ Γ₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r₁.Matches (s₁ ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (mul r₁ r₂) (s₁ ++ s₂) (Γ₁ ++ Γ₂)
  | star_nil {r : Regex α} :
    POSIX r.star [] []
  | stars {r : Regex α} {s₁ s₂ : List α} {Γ₁ Γ₂ : List (String × List α)} :
    POSIX r s₁ Γ₁ →
    POSIX (star r) s₂ Γ₂ →
    s₁ ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r.Matches (s₁ ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (star r) (s₁ ++ s₂) (Γ₁ ++ Γ₂)
  | group {n : String} {cs : List α} {r : Regex α} {s : List α} {Γ : List (String × List α)} :
    POSIX r s Γ →
    POSIX (group n cs r) s ((n, cs ++ s) :: Γ)

theorem POSIX.matches {α : Type u} {r : Regex α} {s : List α} {Γ : List (String × List α)} :
  POSIX r s Γ → r.Matches s := by
  intro h
  induction h with
  | epsilon => exact Matches.epsilon
  | char c => exact Matches.char
  | left h ih => exact Matches.plus_left ih
  | right h hn ih => exact Matches.plus_right ih
  | mul h₁ h₂ hn ih₁ ih₂ =>
    exact Matches.mul rfl ih₁ ih₂
  | star_nil => exact Matches.star_nil
  | stars h₁ h₂ hv hn ih₁ ih₂ =>
    exact Matches.stars hv rfl ih₁ ih₂
  | group h ih => exact Matches.group ih

theorem POSIX.submatches {r : Regex α} {s : List α} {Γ : List (String × List α)} :
  POSIX r s Γ → Submatches s r Γ := by
  intro h
  induction h with
  | epsilon => exact Submatches.epsilon
  | char c => exact Submatches.char
  | left h ih => exact Submatches.left ih
  | right h hn ih => exact Submatches.right ih
  | mul h₁ h₂ hn ih₁ ih₂ =>
    exact Submatches.mul ih₁ ih₂
  | star_nil => exact Submatches.star_nil
  | stars h₁ h₂ hv hn ih₁ ih₂ =>
    exact Submatches.stars ih₁ ih₂
  | group h ih => exact Submatches.group ih

theorem POSIX_markEmpty {α : Type u} {r : Regex α} {s : List α} {Γ : List (String × List α)} :
  POSIX r.markEmpty s Γ → s = [] := by
  intro h
  exact markEmpty_matches_nil h.matches

theorem POSIX_nil_markEmpty {α : Type u} {r : Regex α} {Γ : List (String × List α)} :
  POSIX r.markEmpty [] Γ ↔ POSIX r [] Γ := by
  induction r generalizing Γ with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon => rfl
  | char c => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    constructor
    · intro h
      cases h with
      | left h =>
        rw [ih₁] at h
        exact POSIX.left h
      | right h hn =>
        rw [ih₂] at h
        rw [←nullable_iff_matches_nil, markEmpty_nullable, nullable_iff_matches_nil] at hn
        exact POSIX.right h hn
    · intro h
      cases h with
      | left h =>
        rw [←ih₁] at h
        exact POSIX.left h
      | right h hn =>
        rw [←ih₂] at h
        rw [←nullable_iff_matches_nil, ←markEmpty_nullable, nullable_iff_matches_nil] at hn
        exact POSIX.right h hn
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty]
    constructor
    · intro h
      generalize hs : [] = s at h
      cases h with
      | mul h₁ h₂ hn =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [ih₁] at h₁
        rw [ih₂] at h₂
        exact POSIX.mul h₁ h₂ (by simp_all)
    · intro h
      generalize hs : [] = s at h
      cases h with
      | mul h₁ h₂ hn =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [←ih₁] at h₁
        rw [←ih₂] at h₂
        exact POSIX.mul h₁ h₂ (by simp_all)
  | star r =>
    rw [markEmpty]
    constructor
    · intro h
      generalize hs : [] = s at h
      cases h with
      | star_nil => exact POSIX.star_nil
      | stars _ _ hs₁ =>
        simp at hs
        exact absurd hs.left hs₁
    · intro h
      generalize hs : [] = s at h
      cases h with
      | star_nil => exact POSIX.star_nil
      | stars _ _ hs₁ =>
        simp at hs
        exact absurd hs.left hs₁
  | group n s r ih =>
    rw [markEmpty]
    constructor
    · intro h
      cases h with
      | group h =>
        rw [ih] at h
        exact POSIX.group h
    · intro h
      cases h with
      | group h =>
        rw [←ih] at h
        exact POSIX.group h
