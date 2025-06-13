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
  | mul r₁ r₂ ih₁ ih₂ => sorry
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
