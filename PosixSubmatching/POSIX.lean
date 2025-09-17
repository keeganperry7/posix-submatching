import PosixSubmatching.Regex

open Regex

universe u

variable {α : Type u}

inductive POSIX : List α → Regex α → SubmatchEnv α → Prop
  | epsilon : POSIX [] epsilon []
  | char (c : α) : POSIX [c] (char c) []
  | left {r₁ r₂ : Regex α} {s : List α} {Γ : SubmatchEnv α} :
    POSIX s r₁ Γ →
    POSIX s (plus r₁ r₂) Γ
  | right {r₁ r₂ : Regex α} {s : List α} {Γ : SubmatchEnv α} :
    POSIX s r₂ Γ →
    ¬r₁.Matches s →
    POSIX s (plus r₁ r₂) Γ
  | mul {r₁ r₂ : Regex α} {s s₁ s₂ : List α} {Γ Γ₁ Γ₂ : SubmatchEnv α} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    POSIX s₁ r₁ Γ₁ →
    POSIX s₂ r₂ Γ₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r₁.Matches (s₁ ++ s₃) ∧ r₂.Matches s₄) →
    POSIX s (mul r₁ r₂) Γ
  | star_nil {r : Regex α} :
    POSIX [] r.star []
  | stars {r : Regex α} {s s₁ s₂ : List α} {Γ Γ₁ Γ₂ : SubmatchEnv α} :
    s₁ ++ s₂ = s →
    Γ₁ ++ Γ₂ = Γ →
    POSIX s₁ r Γ₁ →
    POSIX s₂ (star r) Γ₂ →
    s₁ ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ r.Matches (s₁ ++ s₃) ∧ (star r).Matches s₄) →
    POSIX s (star r) Γ
  | group {n : Nat} {s cs : List α} {r : Regex α} {Γ : SubmatchEnv α} :
    POSIX s r Γ →
    POSIX s (group n cs r) ((n, cs ++ s) :: Γ)

example :
  POSIX
    -- "ab"
    ['a', 'b']
    -- (₁ab + a)(₂b + ε)
    (mul
      (group 1 [] (plus (mul (char 'a') (char 'b')) (char 'a')))
      (group 2 [] (plus (char 'b') epsilon)))
    -- {1 ↦ "ab", 2 ↦ []}
    [(1, ['a', 'b']), (2, [])] := by
    refine POSIX.mul rfl rfl
      (POSIX.group (
        POSIX.left
          (POSIX.mul rfl rfl (POSIX.char 'a') (POSIX.char 'b') ?_)))
      (POSIX.group
        (POSIX.right POSIX.epsilon nofun))
      (by simp)
    simp
    intro _ _ _ _ h
    cases h
    contradiction

theorem POSIX.matches {r : Regex α} {s : List α} {Γ : SubmatchEnv α} :
  POSIX s r Γ → r.Matches s := by
  intro h
  induction h with
  | epsilon => exact Matches.epsilon
  | char c => exact Matches.char
  | left h ih => exact Matches.plus_left ih
  | right h hn ih => exact Matches.plus_right ih
  | mul hs _ h₁ h₂ hn ih₁ ih₂ => exact Matches.mul hs ih₁ ih₂
  | star_nil => exact Matches.star_nil
  | stars hs _ h₁ h₂ hv hn ih₁ ih₂ => exact Matches.stars hs ih₁ ih₂
  | group h ih => exact Matches.group ih

theorem POSIX.submatches {r : Regex α} {s : List α} {Γ : SubmatchEnv α} :
  POSIX s r Γ → Submatches s r Γ := by
  intro h
  induction h with
  | epsilon => exact Submatches.epsilon
  | char c => exact Submatches.char
  | left h ih => exact Submatches.left ih
  | right h hn ih => exact Submatches.right ih
  | mul hs hg h₁ h₂ hn ih₁ ih₂ => exact Submatches.mul hs hg ih₁ ih₂
  | star_nil => exact Submatches.star_nil
  | stars hs hg h₁ h₂ hv hn ih₁ ih₂ => exact Submatches.stars hs hg ih₁ ih₂
  | group h ih => exact Submatches.group ih

theorem POSIX_markEmpty {r : Regex α} {s : List α} {Γ : SubmatchEnv α} :
  POSIX s r.markEmpty Γ → s = [] := by
  intro h
  exact markEmpty_matches_nil h.matches

theorem POSIX_nil_markEmpty {r : Regex α} {Γ : SubmatchEnv α} :
  POSIX [] r.markEmpty Γ ↔ POSIX [] r Γ := by
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
      cases h with
      | mul hs hg h₁ h₂ hn =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [ih₁] at h₁
        rw [ih₂] at h₂
        exact POSIX.mul rfl hg h₁ h₂ (by simp_all)
    · intro h
      cases h with
      | mul hs hg h₁ h₂ hn =>
        simp at hs
        cases hs.left
        cases hs.right
        rw [←ih₁] at h₁
        rw [←ih₂] at h₂
        exact POSIX.mul rfl hg h₁ h₂ (by simp_all)
  | star r =>
    rw [markEmpty]
    constructor
    · intro h
      cases h with
      | star_nil => exact POSIX.star_nil
      | stars hs _ _ _ hs₁ =>
        simp at hs
        exact absurd hs.left hs₁
    · intro h
      cases h with
      | star_nil => exact POSIX.star_nil
      | stars hs _ _ _ hs₁ =>
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

theorem longest_split_unique {P₁ P₂ : List α → Prop} {s₁₁ s₁₂ s₂₁ s₂₂ : List α}
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

theorem POSIX.unique {r : Regex α} {s : List α} {Γ₁ Γ₂ : SubmatchEnv α}
  (h₁ : POSIX s r Γ₁) (h₂ : POSIX s r Γ₂) :
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
  | @mul r₁ r₂ _ _ _ _ _ _ hs hg h₁₁ h₁₂ hn ih₁ ih₂ =>
    cases h₂ with
    | mul hs' hg' h₂₁ h₂₂ hn' =>
      rw [←hs'] at hs
      have hs' :=
        longest_split_unique
          hs
          h₁₁.matches h₁₂.matches
          h₂₁.matches h₂₂.matches
          hn hn'
      cases hs'.left
      cases hs'.right
      rw [←hg, ←hg']
      rw [ih₁ h₂₁, ih₂ h₂₂]
  | star_nil =>
    cases h₂ with
    | star_nil => rfl
    | stars hs _ _ _ hs' =>
      simp at hs
      exact absurd hs.left hs'
  | @stars r _ s₁ s₂ _ _ _ hs hg h₁₁ h₁₂ hs₁ hn ih₁ ih₂ =>
    cases h₂ with
    | star_nil =>
      simp at hs
      exact absurd hs.left hs₁
    | stars hs' hg' h₂₁ h₂₂ _ hn' =>
      rw [←hs'] at hs
      have hs' :=
        longest_split_unique
          hs
          h₁₁.matches h₁₂.matches
          h₂₁.matches h₂₂.matches
          hn hn'
      cases hs'.left
      cases hs'.right
      rw [←hg, ←hg']
      rw [ih₁ h₂₁, ih₂ h₂₂]
  | group h₁ ih =>
    cases h₂ with
    | group h₂ => simp [ih h₂]
