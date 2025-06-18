import PosixSubmatching.Regex
import PosixSubmatching.Value
import Mathlib.Tactic.GeneralizeProofs

universe u

variable {α : Type u}

open Regex

theorem extract_extract'_nil {r : Regex α} (hn : r.nullable) :
  r.extract hn = r.extract' (r.mkeps hn) := by
  induction r with
  | emptyset => simp at hn
  | epsilon =>
    simp [extract, extract']
  | char _ => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [extract, mkeps]
    split_ifs with hn₁
    · simp [extract']
      rw [ih₁ hn₁]
    · simp [extract']
      rw [ih₂ (Or.resolve_left hn hn₁)]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [extract, mkeps, extract']
    rw [ih₁ hn.left, ih₂ hn.right]
  | star r ih =>
    simp [extract, mkeps, extract']
  | group n k r ih =>
    simp at hn
    simp [extract, mkeps, extract']
    rw [ih hn]
    simp only [and_true]
    exact mkeps_flat hn

theorem extract_markEmpty {r : Regex α} {v : Value α} (hv : Inhab v r.markEmpty) :
  r.markEmpty.extract' ⟨v, hv⟩ = r.extract' ⟨v, inhab_markEmpty hv⟩ := by
  match r with
  | emptyset => nomatch hv
  | epsilon =>
    simp [markEmpty]
  | char c => nomatch hv
  | plus r₁ r₂ =>
    cases hv with
    | left hv =>
      simp only [markEmpty, extract']
      rw [extract_markEmpty hv]
    | right hv =>
      simp only [markEmpty, extract']
      rw [extract_markEmpty hv]
  | mul r₁ r₂ =>
    cases hv with
    | seq hv₁ hv₂ =>
      simp only [markEmpty, extract']
      rw [extract_markEmpty hv₁, extract_markEmpty hv₂]
  | star r =>
    cases hv with
    | star_nil =>
      simp only [markEmpty, extract']
    | stars hv hvs =>
      simp only [markEmpty, extract']
      rw [extract_markEmpty hv]
      rw [←markEmpty] at hvs
      rw [←extract_markEmpty hvs]
      rfl
  | group n s r =>
    simp only [markEmpty, extract']
    rw [extract_markEmpty]

variable [DecidableEq α]

theorem extract_deriv (r : Regex α) (x : α) (v : Value α) (hv : Inhab v (r.deriv x)) :
  (r.deriv x).extract' ⟨v, hv⟩ = r.extract' (inj r x ⟨v, hv⟩) := by
  induction r generalizing v with
  | emptyset => nomatch hv
  | epsilon => nomatch hv
  | char c =>
    simp only [inj, extract']
    generalize hr : (char c).deriv x = r' at hv
    rw [deriv] at hr
    split_ifs at hr
    · subst hr
      rw [extract']
    · subst hr
      nomatch hv
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hv with
    | left hv =>
      simp [extract', inj]
      rw [ih₁]
    | right hv =>
      simp [extract', inj]
      rw [ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [inj]
    split_ifs with hn
    · split
      · rw [extract', ←ih₁]
        generalize_proofs
        generalize hr : (r₁.mul r₂).deriv x = r' at hv
        simp [deriv, hn] at hr
        subst hr
        rw [extract', extract']
      · rw [extract', ←ih₂]
        generalize_proofs
        generalize hr : (r₁.mul r₂).deriv x = r' at hv
        simp [deriv, hn] at hr
        subst hr
        rw [extract', extract']
        rw [extract_markEmpty]
    · split
      rw [extract', ←ih₁]
      generalize_proofs
      generalize hr : (r₁.mul r₂).deriv x = r' at hv
      simp [deriv, hn] at hr
      subst hr
      rw [extract']
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj, extract']
      rw [ih]
  | group n s r ih =>
    simp [deriv, inj, extract', ih]
    rw [inj_flat]

theorem captures_captures' (r : Regex α) (s : List α) :
  r.captures s = r.captures' s := by
  induction s generalizing r with
  | nil =>
    rw [captures, captures']
    split_ifs with hn
    · exact extract_extract'_nil hn
    · rfl
  | cons x xs ih =>
    simp [captures, derivs]
    split_ifs with hn
    · have ih := ih (r.deriv x)
      simp [captures, hn] at ih
      rw [ih]
      simp [captures', hn, injs]
      rw [extract_deriv]
    · simp [captures', hn]

theorem parse_iff_matches (r : Regex α) (s : List α) :
  (r.parse s).isSome ↔ r.Matches s := by
  induction s generalizing r with
  | nil =>
    simp [parse]
    exact nullable_iff_matches_nil
  | cons x xs ih =>
    rw [Matches_deriv, ←ih]
    simp [parse]
