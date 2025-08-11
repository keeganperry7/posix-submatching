import PosixSubmatching.Regex

open Regex

universe u

variable {α : Type u}

inductive POSIX : Regex α → List α → List (Nat × List α) → Prop
  | epsilon : POSIX epsilon [] []
  | char (c : α) : POSIX (char c) [c] []
  | left {r₁ r₂ : Regex α} {s : List α} {Γ : List (Nat × List α)} :
    POSIX r₁ s Γ →
    POSIX (plus r₁ r₂) s Γ
  | right {r₁ r₂ : Regex α} {s : List α} {Γ : List (Nat × List α)} :
    POSIX r₂ s Γ →
    ¬r₁.Matches s →
    POSIX (plus r₁ r₂) s Γ
  | mul {r₁ r₂ : Regex α} {s₁ s₂ : List α} {Γ₁ Γ₂ : List (Nat × List α)} :
    POSIX r₁ s₁ Γ₁ →
    POSIX r₂ s₂ Γ₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r₁.Matches (s₁ ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (mul r₁ r₂) (s₁ ++ s₂) (Γ₁ ++ Γ₂)
  | star_nil {r : Regex α} :
    POSIX r.star [] []
  | stars {r : Regex α} {s₁ s₂ : List α} {Γ₁ Γ₂ : List (Nat × List α)} :
    POSIX r s₁ Γ₁ →
    POSIX (star r) s₂ Γ₂ →
    s₁ ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r.Matches (s₁ ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (star r) (s₁ ++ s₂) (Γ₁ ++ Γ₂)
  | group {n : Nat} {cs : List α} {r : Regex α} {s : List α} {Γ : List (Nat × List α)} :
    POSIX r s Γ →
    POSIX (group n cs r) s ((n, cs ++ s) :: Γ)

theorem POSIX.matches {r : Regex α} {s : List α} {Γ : List (Nat × List α)} :
  POSIX r s Γ → r.Matches s := by
  intro h
  induction h with
  | epsilon => exact Matches.epsilon
  | char c => exact Matches.char
  | left h ih => exact Matches.plus_left ih
  | right h hn ih => exact Matches.plus_right ih
  | mul h₁ h₂ hn ih₁ ih₂ => exact Matches.mul rfl ih₁ ih₂
  | star_nil => exact Matches.star_nil
  | stars h₁ h₂ hv hn ih₁ ih₂ => exact Matches.stars rfl ih₁ ih₂
  | group h ih => exact Matches.group ih

theorem POSIX.submatches {r : Regex α} {s : List α} {Γ : List (Nat × List α)} :
  POSIX r s Γ → Submatches s r Γ := by
  intro h
  induction h with
  | epsilon => exact Submatches.epsilon
  | char c => exact Submatches.char
  | left h ih => exact Submatches.left ih
  | right h hn ih => exact Submatches.right ih
  | mul h₁ h₂ hn ih₁ ih₂ => exact Submatches.mul ih₁ ih₂
  | star_nil => exact Submatches.star_nil
  | stars h₁ h₂ hv hn ih₁ ih₂ => exact Submatches.stars ih₁ ih₂
  | group h ih => exact Submatches.group ih

theorem POSIX_markEmpty {r : Regex α} {s : List α} {Γ : List (Nat × List α)} :
  POSIX r.markEmpty s Γ → s = [] := by
  intro h
  exact markEmpty_matches_nil h.matches

theorem POSIX_nil_markEmpty {r : Regex α} {Γ : List (Nat × List α)} :
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

theorem longest_split_unique (P₁ P₂ : List α → Prop) {s₁₁ s₁₂ s₂₁ s₂₂ : List α}
  (hs : s₁₁ ++ s₁₂ = s₂₁ ++ s₂₂)
  (hr₁₁ : P₁ s₁₁) (hr₁₂ : P₂ s₁₂)
  (hr₂₁ : P₁ s₂₁) (hr₂₂ : P₂ s₂₂)
  (h₁ : ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₁₂ ∧ P₁ (s₁₁ ++ s₃) ∧ P₂ s₄))
  (h₂ : ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂₂ ∧ P₁ (s₂₁ ++ s₃) ∧ P₂ s₄)) :
  s₁₁ = s₂₁ ∧ s₁₂ = s₂₂ := by
  rw [List.append_eq_append_iff] at hs
  cases hs with
  | inl hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      exact absurd hr₂₂ (h₁ (x::xs) (by simp) s₂₂ rfl hr₂₁)
  | inr hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      exact absurd hr₁₂ (h₂ (x::xs) (by simp) s₁₂ rfl hr₁₁)

theorem POSIX.unique {r : Regex α} {s : List α} {Γ₁ Γ₂ : List (Nat × List α)}
  (h₁ : POSIX r s Γ₁) (h₂ : POSIX r s Γ₂) :
  Γ₁ = Γ₂ := by
  induction h₁ generalizing Γ₂ with
  | epsilon =>
    cases h₂
    rfl
  | char c =>
    cases h₂
    rfl
  | left h₁ ih =>
    cases h₂ with
    | left h₂ => exact ih h₂
    | right h₂ hn => exact absurd h₁.matches hn
  | right h₁ hn ih =>
    cases h₂ with
    | left h₂ => exact absurd h₂.matches hn
    | right h₂ hn' => exact ih h₂
  | @mul r₁ r₂ s₁ s₂ _ _ h₁₁ h₁₂ hn ih₁ ih₂ =>
    generalize hs : s₁ ++ s₂ = s at h₂
    cases h₂ with
    | mul h₂₁ h₂₂ hn' =>
      have hs' :=
        longest_split_unique
          r₁.Matches _
          hs
          h₁₁.matches h₁₂.matches
          h₂₁.matches h₂₂.matches
          hn hn'
      cases hs'.left
      cases hs'.right
      rw [ih₁ h₂₁, ih₂ h₂₂]
  | star_nil =>
    generalize hs : [] = s at h₂
    cases h₂ with
    | star_nil => rfl
    | stars _ _ hs' =>
      simp at hs
      exact absurd hs.left hs'
  | @stars r s₁ s₂ _ _ h₁₁ h₁₂ hs₁ hn ih₁ ih₂ =>
    generalize hs : s₁ ++ s₂ = s at h₂
    cases h₂ with
    | star_nil =>
      simp at hs
      exact absurd hs.left hs₁
    | stars h₂₁ h₂₂ _ hn' =>
      have hs' :=
        longest_split_unique
          r.Matches _
          hs
          h₁₁.matches h₁₂.matches
          h₂₁.matches h₂₂.matches
          hn hn'
      cases hs'.left
      cases hs'.right
      rw [ih₁ h₂₁, ih₂ h₂₂]
  | group h₁ ih =>
    cases h₂ with
    | group h₂ => simp [ih h₂]
