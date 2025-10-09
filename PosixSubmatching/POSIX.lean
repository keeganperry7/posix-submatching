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
  | and {r₁ r₂ : Regex α} {s : List α} {Γ Γ₁ Γ₂ : SubmatchEnv α} :
    Γ₁ ++ Γ₂ = Γ →
    POSIX s r₁ Γ₁ →
    POSIX s r₂ Γ₂ →
    POSIX s (and r₁ r₂) Γ
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
  | not {r : Regex α} {s : List α} :
    ¬r.Matches s →
    POSIX s (not r) []
  | group {n : Nat} {s cs : List α} {r : Regex α} {Γ : SubmatchEnv α} :
    POSIX s r Γ →
    POSIX s (group n cs r) ((n, cs ++ s) :: Γ)

theorem POSIX.matches {r : Regex α} {s : List α} {Γ : SubmatchEnv α} :
  POSIX s r Γ → r.Matches s := by
  intro h
  induction h with
  | epsilon =>
    rw [Matches]
  | char c =>
    rw [Matches]
  | left h ih =>
    rw [Matches]
    exact Or.inl ih
  | right h hn ih =>
    rw [Matches]
    exact Or.inr ih
  | mul hs _ h₁ h₂ hn ih₁ ih₂ =>
    rw [Matches]
    exact ⟨_, _, hs, ih₁, ih₂⟩
  | and _ h₁ h₂ ih₁ ih₂ =>
    rw [Matches]
    exact ⟨ih₁, ih₂⟩
  | star_nil =>
    rw [Matches]
    exact ⟨[], by simp⟩
  | stars hs _ h₁ h₂ hv hn ih₁ ih₂ =>
    rw [matches_star_iff]
    exact Or.inr ⟨_, _, hv, hs, ih₁, ih₂⟩
  | not h =>
    rw [Matches]
    exact h
  | group h ih =>
    rw [Matches]
    exact ih

theorem POSIX.submatches {r : Regex α} {s : List α} {Γ : SubmatchEnv α} :
  POSIX s r Γ → Submatches r s Γ := by
  intro h
  induction h with
  | epsilon =>
    simp [Submatches]
  | char c =>
    simp [Submatches]
  | left h ih =>
    rw [Submatches]
    exact Or.inl ih
  | right h hn ih =>
    rw [Submatches]
    exact Or.inr ih
  | mul hs hg h₁ h₂ hn ih₁ ih₂ =>
    rw [Submatches]
    exact ⟨_, _, _, _, hs, hg, ih₁, ih₂⟩
  | and hg h₁ h₂ ih₁ ih₂ =>
    rw [Submatches]
    exact ⟨_, _, hg, ih₁, ih₂⟩
  | star_nil =>
    rw [Submatches]
    exact ⟨[], by simp⟩
  | @stars _ s s₁ s₂ Γ Γ₁ Γ₂ hs hg h₁ h₂ hv hn ih₁ ih₂ =>
    rw [Submatches] at *
    rcases ih₂ with ⟨L, hs₂, hΓ₂, ih₂⟩
    subst hs hg
    refine ⟨(s₁, Γ₁) :: L, by simp [hs₂], by simp [hΓ₂], ?_⟩
    simp at ih₂
    simp [ih₁]
    exact ih₂
  | not h =>
    simp [Matches_iff_exists_Submatches] at h
    rw [Submatches]
    simp
    intro Γ' h'
    exact absurd h' (h Γ')
  | group h ih =>
    simp [Submatches]
    exact ih

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
        rw [←nullable_iff_matches_nil, markEmpty_nullable] at hn
        rw [nullable_iff_matches_nil] at hn
        exact POSIX.right h hn
    · intro h
      cases h with
      | left h =>
        rw [←ih₁] at h
        exact POSIX.left h
      | right h hn =>
        rw [←ih₂] at h
        rw [←nullable_iff_matches_nil, ←markEmpty_nullable] at hn
        rw [nullable_iff_matches_nil] at hn
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
  | and r₁ r₂ ih₁ ih₂ =>
    rw [markEmpty]
    constructor
    · intro h
      cases h with
      | and hg h₁ h₂ =>
        rw [ih₁] at h₁
        rw [ih₂] at h₂
        exact POSIX.and hg h₁ h₂
    · intro h
      cases h with
      | and hg h₁ h₂ =>
        rw [←ih₁] at h₁
        rw [←ih₂] at h₂
        exact POSIX.and hg h₁ h₂
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
  | not r ih =>
    rw [markEmpty]
    split
    · case isTrue hn =>
      constructor
      · nofun
      · intro h
        cases h with
        | not h =>
          rw [nullable_iff_matches_nil] at hn
          exact absurd hn h
    · case isFalse hn =>
      constructor
      · intro h
        rw [nullable_iff_matches_nil] at hn
        cases h
        exact POSIX.not hn
      · intro h
        cases h
        exact POSIX.epsilon
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
  | and hg₁ h₁₁ h₁₂ ih₁ ih₂ =>
    cases h₂ with
    | and hg₂ h₂₁ h₂₂ =>
      subst hg₁ hg₂
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
  | not h₁ =>
    cases h₂
    rfl
  | group h₁ ih =>
    cases h₂ with
    | group h₂ => simp [ih h₂]
