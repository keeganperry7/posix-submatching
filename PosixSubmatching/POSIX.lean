import PosixSubmatching.Value

open Regex
open Value

universe u

variable {α : Type u}

inductive POSIX : Regex α → Value α → Prop
  | epsilon : POSIX epsilon empty
  | char (c : α) : POSIX (char c) (char c)
  | left {r₁ r₂ : Regex α} {v : Value α} :
    POSIX r₁ v →
    POSIX (plus r₁ r₂) (left v)
  | right {r₁ r₂ : Regex α} {v : Value α} :
    POSIX r₂ v →
    ¬r₁.Matches v.flat →
    POSIX (plus r₁ r₂) (right v)
  | mul {r₁ r₂ : Regex α} {v₁ v₂ : Value α} :
    POSIX r₁ v₁ →
    POSIX r₂ v₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = v₂.flat ∧ r₁.Matches (v₁.flat ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (mul r₁ r₂) (seq v₁ v₂)
  | star_nil {r : Regex α} :
    POSIX (star r) (stars [])
  | stars {r : Regex α} {v : Value α} {vs : List (Value α)} :
    POSIX r v →
    POSIX (star r) (stars vs) →
    v.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = (stars vs).flat ∧ r.Matches (v.flat ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (star r) (stars (v::vs))
  | group {n : String} {s : List α} {r : Regex α} {v : Value α} :
    POSIX r v →
    POSIX (group n s r) v

theorem POSIX_inhab {r : Regex α} {v : Value α} :
  POSIX r v → Inhab v r := by
  intro h
  induction h with
  | epsilon => exact Inhab.empty
  | char c => exact Inhab.char c
  | left h ih => exact Inhab.left ih
  | right h hn ih => exact Inhab.right ih
  | mul h₁ h₂ hn ih₁ ih₂ => exact Inhab.seq ih₁ ih₂
  | star_nil => exact Inhab.star_nil
  | stars h₁ h₂ hv hn ih₁ ih₂ => exact Inhab.stars ih₁ ih₂
  | group h ih => exact Inhab.group ih

theorem mkeps_posix {r : Regex α} (hn : r.nullable) :
  POSIX r (r.mkeps hn).fst := by
  induction r with
  | emptyset => simp [nullable] at hn
  | epsilon =>
    simp only [mkeps]
    apply POSIX.epsilon
  | char => simp [nullable] at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp only [mkeps]
    split_ifs with hn'
    · exact POSIX.left (ih₁ hn')
    · apply POSIX.right
      exact ih₂ (Or.resolve_left hn hn')
      rw [mkeps_flat]
      rw [←nullable_iff_matches_nil]
      exact hn'
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp only [mkeps]
    apply POSIX.mul
    exact ih₁ hn.left
    exact ih₂ hn.right
    rw [mkeps_flat]
    simp_all
  | star r ih =>
    simp only [mkeps]
    apply POSIX.star_nil
  | group n s r ih =>
    rw [nullable] at hn
    exact POSIX.group (ih hn)

theorem posix_markEmpty {r : Regex α} {v : Value α} :
  POSIX r.markEmpty v → POSIX r v := by
  intro h
  match r with
  | emptyset => nomatch h
  | epsilon => exact h
  | .char c => nomatch h
  | .plus r₁ r₂  =>
    cases h with
    | left h =>
      exact POSIX.left (posix_markEmpty h)
    | right h hn =>
      refine POSIX.right (posix_markEmpty h) ?_
      rw [inhab_markEmpty_flat (POSIX_inhab h)] at *
      rw [←nullable_iff_matches_nil] at *
      rw [markEmpty_nullable] at hn
      exact hn
  | .mul r₁ r₂ =>
    rw [markEmpty] at h
    cases h with
    | mul h₁ h₂ hn =>
      apply POSIX.mul
      exact posix_markEmpty h₁
      exact posix_markEmpty h₂
      rw [inhab_markEmpty_flat (POSIX_inhab h₁)] at *
      rw [inhab_markEmpty_flat (POSIX_inhab h₂)] at *
      simp_all
  | .star r =>
    rw [markEmpty] at h
    cases h with
    | star_nil => exact POSIX.star_nil
    | stars h₁ h₂ hv hn =>
      apply POSIX.stars
      exact posix_markEmpty h₁
      exact posix_markEmpty h₂
      exact hv
      rw [inhab_markEmpty_flat (POSIX_inhab h₁)] at *
      simp_all
  | .group n s r =>
    cases h with
    | group h => exact POSIX.group (posix_markEmpty h)

variable [DecidableEq α]

theorem posix_deriv (r : Regex α) (v : Value α) (c : α) (h : POSIX (r.deriv c) v) :
  POSIX r (inj r c ⟨v, POSIX_inhab h⟩).fst := by
  induction r generalizing v with
  | emptyset =>
    simp at h
    cases h
  | epsilon =>
    simp at h
    cases h
  | char d =>
    simp [deriv] at h
    split_ifs at h with hc
    · cases h
      simp [hc] at h
      simp [inj, hc]
      apply POSIX.char
    · cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    match v with
    | Value.left v' =>
      cases h with
      | left h =>
        simp [inj]
        exact POSIX.left (ih₁ _ h)
    | Value.right v' =>
      cases h with
      | right h hn =>
        simp [inj]
        apply POSIX.right
        exact ih₂ _ h
        rw [inj_flat, Matches_deriv]
        exact hn
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [deriv] at h
    split_ifs at h with hn
    · cases h with
      | left h' =>
        simp [hn] at h
        cases h' with
        | mul h₁ h₂ hs =>
          simp [inj, hn]
          apply POSIX.mul
          apply ih₁
          exact h₁
          exact h₂
          simp_rw [inj_flat, List.cons_append, Matches_deriv]
          exact hs
      | right h' hn' =>
        simp [hn] at h
        cases h' with
        | mul h₁ h₂ hs =>
          simp [inj, hn]
          apply POSIX.mul
          exact posix_markEmpty h₁
          exact ih₂ _ h₂
          simp_rw [inhab_markEmpty_flat (POSIX_inhab h₁), inj_flat]
          simp
          intro x hx y hxy hr₁ hr₂
          rw [List.append_eq_cons_iff] at hxy
          simp [hx] at hxy
          rcases hxy with ⟨z, hx, hs⟩
          rw [hx] at hr₁
          rw [Matches_deriv] at hr₁
          simp [flat, inhab_markEmpty_flat (POSIX_inhab h₁)] at hn'
          rw [Matches_mul] at hn'
          simp at hn'
          exact absurd hr₂ (hn' z y (by simp [hs]) hr₁)
    · cases h with
      | mul h₁ h₂ hn' =>
        simp [inj, hn]
        apply POSIX.mul
        apply ih₁
        exact h₁
        exact h₂
        simp_rw [inj_flat, List.cons_append, Matches_deriv]
        exact hn'
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj]
      cases h with
      | mul h₁ h₂ hs =>
        apply POSIX.stars
        apply ih
        exact h₁
        exact h₂
        simp [inj_flat]
        simp_rw [inj_flat, List.cons_append, Matches_deriv]
        exact hs
  | group n k r ih =>
    rw [deriv] at h
    cases h with
    | group h => exact POSIX.group (ih _ h)

theorem posix_derivs (r : Regex α) (v : Value α) (s : List α) (h : POSIX (r.derivs s) v) :
  POSIX r (injs r s ⟨v, POSIX_inhab h⟩).fst := by
  induction s generalizing r with
  | nil =>
    rw [derivs] at h
    exact h
  | cons x xs ih =>
    rw [derivs] at h
    simp [injs]
    apply posix_deriv
    exact ih _ h

theorem parse_posix (r : Regex α) (s : List α) (v : Value α) (h : r.parse s = some v) :
  POSIX r v := by
  induction s generalizing r v with
  | nil =>
    simp [parse, injs] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    exact mkeps_posix hn
  | cons x xs ih =>
    simp [parse, injs] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    apply posix_deriv
    apply ih
    simp [parse, hn]
