import PosixSubmatching.Regex
import PosixSubmatching.POSIX
import Mathlib.Tactic.GeneralizeProofs

universe u

variable {α : Type u}

open Regex

theorem extract_nil_posix {α : Type u} {r : Regex α} {Γ : List (String × List α)} :
  (∃ hr : r.nullable, r.extract hr = Γ) ↔ POSIX r [] Γ := by
  induction r generalizing Γ with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon =>
    simp [extract]
    constructor
    · intro h
      subst h
      exact POSIX.epsilon
    · intro h
      cases h
      rfl
  | char c => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [extract]
    split_ifs with hr₁
    · constructor
      · intro ⟨hr, h⟩
        exact POSIX.left (ih₁.mp ⟨hr₁, h⟩)
      · intro h
        cases h with
        | left h =>
          rw [←ih₁] at h
          rcases h with ⟨_, h⟩
          exact ⟨Or.inl hr₁, h⟩
        | right h hn =>
          rw [nullable_iff_matches_nil] at hr₁
          exact absurd hr₁ hn
    · constructor
      · intro ⟨hr, h⟩
        refine POSIX.right (ih₂.mp ⟨Or.resolve_left hr hr₁, h⟩) ?_
        rw [nullable_iff_matches_nil] at hr₁
        exact hr₁
      · intro h
        cases h with
        | left h =>
          rw [nullable_iff_matches_nil] at hr₁
          exact absurd (POSIX_matches h) hr₁
        | right h hn =>
          rw [←ih₂] at h
          rcases h with ⟨hr₂, h⟩
          exact ⟨Or.inr hr₂, h⟩
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [extract]
    constructor
    · intro ⟨hr, h⟩
      rw [←h]
      rw [←List.nil_append []]
      apply POSIX.mul
      simp [←ih₁, hr.left]
      simp [←ih₂, hr.right]
      simp_all
    · intro h
      generalize hs : [] = s at h
      cases h with
      | mul h₁ h₂ hn =>
        simp at hs
        rw [hs.left, ←ih₁] at h₁
        rcases h₁ with ⟨hr₁, h₁⟩
        rw [hs.right, ←ih₂] at h₂
        rcases h₂ with ⟨hr₂, h₂⟩
        simp [h₁, h₂, hr₁, hr₂]
  | star r ih =>
    simp [extract]
    constructor
    · intro h
      subst h
      exact POSIX.star_nil
    · intro h
      generalize hs : [] = s at h
      cases h with
      | star_nil => rfl
      | stars h₁ h₂ hs₁ hn =>
        simp at hs
        exact absurd hs.left hs₁
  | group n s r ih =>
    simp [extract]
    constructor
    · intro ⟨hr, h⟩
      rw [←List.append_nil s] at h
      subst h
      apply POSIX.group
      simp [←ih, hr]
    · intro h
      cases h with
      | group h =>
        simp [ih]
        exact h

variable [DecidableEq α]

theorem posix_deriv {r : Regex α} {c : α} {s : List α} {Γ : List (String × List α)} :
  POSIX r (c::s) Γ ↔ POSIX (r.deriv c) s Γ := by
  induction r generalizing s Γ with
  | emptyset =>
    exact ⟨nofun, nofun⟩
  | epsilon =>
    exact ⟨nofun, nofun⟩
  | char d =>
    constructor
    · intro h
      cases h
      simp
      exact POSIX.epsilon
    · intro h
      simp at h
      split_ifs at h with hc
      · cases h
        cases hc
        exact POSIX.char c
      · nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    constructor
    · intro h
      cases h with
      | left h =>
        rw [ih₁] at h
        exact POSIX.left h
      | right h hn =>
        rw [ih₂] at h
        rw [Matches_deriv] at hn
        exact POSIX.right h hn
    · intro h
      cases h with
      | left h =>
        rw [←ih₁] at h
        exact POSIX.left h
      | right h hn =>
        rw [←ih₂] at h
        rw [←Matches_deriv] at hn
        exact POSIX.right h hn
  | mul r₁ r₂ ih₁ ih₂ =>
    constructor
    · intro h
      generalize hcs : c::s = cs at h
      cases h with
      | @mul _ _ s₁ s₂ _ _ h₁ h₂ hn =>
        simp [deriv]
        split_ifs with hr
        · cases s₁ with
          | nil =>
            simp at hcs
            cases hcs
            rw [ih₂] at h₂
            rw [←POSIX_nil_markEmpty] at h₁
            apply POSIX.right
            rw [←List.nil_append s]
            apply POSIX.mul
            exact h₁
            exact h₂
            simp
            intro x hx _ _ hr₁
            apply markEmpty_matches_nil at hr₁
            exact absurd hr₁ hx
            intro hn'
            cases hn' with
            | @mul s₁ s₂ _ _ _ hs h₁' h₂' =>
              rw [←Matches_deriv] at h₁'
              cases hs
              simp_all
              exact absurd h₂' (hn (c::s₁) (by simp) s₂ (by simp) h₁')
          | cons x xs =>
            simp at hcs
            cases hcs.left
            rw [ih₁] at h₁
            apply POSIX.left
            rw [hcs.right]
            simp_rw [List.cons_append, Matches_deriv] at hn
            exact POSIX.mul h₁ h₂ hn
        · cases s₁ with
          | nil =>
            rw [nullable_iff_matches_nil] at hr
            exact absurd (POSIX_matches h₁) hr
          | cons x xs =>
            simp at hcs
            cases hcs.left
            cases hcs.right
            rw [ih₁] at h₁
            simp_rw [List.cons_append, Matches_deriv] at hn
            exact POSIX.mul h₁ h₂ hn
    · intro h
      simp at h
      split_ifs at h with hr
      · cases h with
        | left h =>
          cases h with
          | mul h₁ h₂ hn =>
            rw [←ih₁] at h₁
            simp_rw [←Matches_deriv, ←List.cons_append] at hn
            rw [←List.cons_append]
            exact POSIX.mul h₁ h₂ hn
        | right h hr₁ =>
          cases h with
          | mul h₁ h₂ hn =>
            rw [←ih₂] at h₂
            cases (POSIX_markEmpty h₁)
            rw [POSIX_nil_markEmpty] at h₁
            simp
            rw [←List.nil_append (c::_)]
            refine POSIX.mul h₁ h₂ ?_
            simp at hr₁
            simp
            intro x₁ hx₁ x₂ hcs h₁' h₂'
            cases x₁ with
            | nil => contradiction
            | cons y ys =>
              simp at hcs
              cases hcs.left
              cases hcs.right
              rw [Matches_deriv] at h₁'
              exact absurd (Matches.mul rfl h₁' h₂') hr₁
      · cases h with
        | mul h₁ h₂ hn =>
          rw [←ih₁] at h₁
          simp_rw [←Matches_deriv, ←List.cons_append] at hn
          rw [←List.cons_append]
          exact POSIX.mul h₁ h₂ hn
  | star r ih =>
    constructor
    · intro h
      generalize hcs : c::s = cs at h
      cases h with
      | star_nil => simp at hcs
      | @stars _ s₁ s₂ _ _ h₁ h₂ hs₁ hn =>
        cases s₁ with
        | nil => nomatch hs₁
        | cons x xs =>
          simp at hcs
          cases hcs.left
          cases hcs.right
          rw [ih] at h₁
          simp_rw [List.cons_append, Matches_deriv] at hn
          exact POSIX.mul h₁ h₂ hn
    · intro h
      cases h with
      | mul h₁ h₂ hn =>
        rw [←ih] at h₁
        rw [←List.cons_append]
        simp_rw [←Matches_deriv, ←List.cons_append] at hn
        exact POSIX.stars h₁ h₂ (by simp) hn
  | group n cs r ih =>
    constructor
    · intro h
      cases h with
      | group h =>
        simp
        rw [ih] at h
        rw [List.append_cons cs c s]
        exact POSIX.group h
    · intro h
      cases h with
      | group h =>
        simp
        rw [←ih] at h
        exact POSIX.group h

theorem captures_posix (r : Regex α) (s : List α) (Γ : List (String × List α)) :
  r.captures s = some Γ ↔ POSIX r s Γ := by
  induction s generalizing r with
  | nil =>
    simp [captures]
    exact extract_nil_posix
  | cons x xs ih =>
    rw [posix_deriv, ←ih]
    simp [captures]

theorem captures_iff_matches (r : Regex α) (s : List α) :
  (r.captures s).isSome ↔ r.Matches s := by
  induction s generalizing r with
  | nil =>
    simp [captures]
    exact nullable_iff_matches_nil
  | cons x xs ih =>
    rw [Matches_deriv, ←ih]
    simp [captures]
