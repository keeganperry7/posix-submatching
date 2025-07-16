import PosixSubmatching.Regex
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Bool.Basic

universe u

inductive Value (α : Type u)
  | empty : Value α
  | char : α → Value α
  | left : Value α → Value α
  | right : Value α → Value α
  | seq : Value α → Value α → Value α
  | stars : List (Value α) → Value α
  deriving Repr

variable {α : Type u}

@[simp]
def Value.flat : Value α → List α
  | empty => []
  | char c => [c]
  | left v => v.flat
  | right v => v.flat
  | seq v₁ v₂ => v₁.flat ++ v₂.flat
  | stars [] => []
  | stars (v::vs) => v.flat ++ (stars vs).flat

open Value
open Regex

inductive Inhab : Value α → Regex α → Prop
  | empty : Inhab empty epsilon
  | char (c : α) : Inhab (char c) (char c)
  | left {v₁ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab (left v₁) (plus r₁ r₂)
  | right {v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₂ r₂ →
    Inhab (right v₂) (plus r₁ r₂)
  | seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab v₂ r₂ →
    Inhab (seq v₁ v₂) (mul r₁ r₂)
  | star_nil {r : Regex α} :
    Inhab (stars []) (star r)
  | stars {v : Value α} {vs : List (Value α)} {r : Regex α} :
    -- v.flat ≠ [] →
    Inhab v r →
    Inhab (stars vs) (star r) →
    Inhab (stars (v::vs)) (star r)
  | group {v : Value α} {n : String} {s : List α} {r : Regex α} :
    Inhab v r →
    Inhab v (group n s r)

@[simp]
theorem inhab_zero {v : Value α} :
  ¬Inhab v emptyset := by
  intro h
  cases h

theorem inhab_left {v₁ : Value α} {r₁ r₂ : Regex α} :
  Inhab (left v₁) (plus r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | left h =>
    exact h

theorem inhab_right {v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (right v₂) (plus r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | right h =>
    exact h

theorem inhab_seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ ∧ Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq h₁ h₂ => exact ⟨h₁, h₂⟩

theorem inhab_seq_fst {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | seq h₁ _ => exact h₁

theorem inhab_seq_snd {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq _ h₂ => exact h₂

theorem inhab_stars_head {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab v r := by
  intro h
  cases h with
  | stars h₁ _ => exact h₁

theorem inhab_stars_tail {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab (stars vs) r.star := by
  intro h
  cases h with
  | stars _ h₂ => exact h₂

theorem inhab_group {v : Value α} {n : String} {s : List α} {r : Regex α} :
  Inhab v (group n s r) → Inhab v r := by
  intro h
  cases h with
  | group h => exact h

theorem inhab_markEmpty {v : Value α} {r : Regex α} :
  Inhab v r.markEmpty → Inhab v r := by
  intro h
  match r with
  | epsilon => exact h
  | plus r₁ r₂ =>
    cases h with
    | left h =>
      exact Inhab.left (inhab_markEmpty h)
    | right h =>
      exact Inhab.right (inhab_markEmpty h)
  | mul r₁ r₂  =>
    cases h with
    | seq h₁ h₂ =>
      exact Inhab.seq (inhab_markEmpty h₁) (inhab_markEmpty h₂)
  | star r =>
    cases h with
    | star_nil => exact Inhab.star_nil
    | stars hv hvs =>
      exact Inhab.stars (inhab_markEmpty hv) (inhab_markEmpty hvs)
  | group n s r =>
    cases h with
    | group h => exact Inhab.group (inhab_markEmpty h)

theorem inhab_markEmpty_flat {v : Value α} {r : Regex α} (hv : Inhab v r.markEmpty) :
  v.flat = [] := by
  match r with
  | epsilon =>
    cases hv
    rw [flat]
  | plus r₁ r₂ =>
    cases hv with
    | left hv =>
      rw [flat, inhab_markEmpty_flat hv]
    | right hv =>
      rw [flat, inhab_markEmpty_flat hv]
  | mul r₁ r₂ =>
    cases hv with
    | seq hv₁ hv₂ =>
      rw [flat, inhab_markEmpty_flat hv₁, inhab_markEmpty_flat hv₂]
      rfl
  | star r =>
    cases hv with
    | star_nil => rw [flat]
    | stars hv hvs =>
      rw [←markEmpty] at hvs
      rw [flat, inhab_markEmpty_flat hv, inhab_markEmpty_flat hvs]
      rfl
  | group n s r =>
    cases hv with
    | group hv =>
      exact inhab_markEmpty_flat hv

theorem  Inhab_not_nullable {r : Regex α} {v : Value α} (hn : ¬r.nullable) (hv : v.flat = []) :
  ¬Inhab v r := by
  intro h
  induction r generalizing v with
  | emptyset => nomatch h
  | epsilon => simp at hn
  | char =>
    cases h with
    | char => simp at hv
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases h with
    | left h =>
      apply ih₁
      simp [hn]
      simp at hv
      exact hv
      exact h
    | right h =>
      apply ih₂
      simp [hn]
      simp at hv
      exact hv
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | seq h₁ h₂ =>
      simp at hv
      simp at hn
      apply ih₁
      intro hn₁
      apply ih₂
      simp [hn hn₁]
      exact hv.right
      exact h₂
      exact hv.left
      exact h₁
  | star r => simp at hn
  | group n s r ih =>
    cases h with
    | group h => exact ih hn hv h

def Regex.mkeps : (r : Regex α) → r.nullable → (Σ' v : Value α, Inhab v r)
  | epsilon, _ => ⟨Value.empty, Inhab.empty⟩
  | plus r₁ r₂, hn =>
    if hn₁ : r₁.nullable
      then
        have ⟨v₁, h₁⟩ := mkeps r₁ hn₁
        ⟨Value.left v₁, Inhab.left h₁⟩
      else
        have ⟨v₂, h₂⟩ := mkeps r₂ (Or.resolve_left (Bool.or_eq_true _ _ ▸ hn) hn₁)
        ⟨Value.right v₂, Inhab.right h₂⟩
  | mul r₁ r₂, hn =>
    have ⟨v₁, h₁⟩ := mkeps r₁ (Bool.and_elim_left hn)
    have ⟨v₂, h₂⟩ := mkeps r₂ (Bool.and_elim_right hn)
    ⟨Value.seq v₁ v₂, Inhab.seq h₁ h₂⟩
  | star _, _ => ⟨Value.stars [], Inhab.star_nil⟩
  | group _ _ r, hn =>
    have ⟨v, h⟩ := mkeps r hn
    ⟨v, Inhab.group h⟩

theorem mkeps_flat {α : Type u} {r : Regex α} (hn : r.nullable) :
  (r.mkeps hn).fst.flat = [] := by
  induction r with
  | emptyset => simp at hn
  | epsilon =>
    simp only [mkeps, Value.flat]
  | char c => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [mkeps]
    split_ifs with hn'
    · rw [Value.flat, ih₁]
    · rw [Value.flat, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [mkeps]
    rw [ih₁, ih₂, and_self]
  | star r ih => simp [mkeps]
  | group n s r ih =>
    simp at hn
    simp [mkeps]
    exact ih hn

variable [DecidableEq α]

def inj : (r : Regex α) → (c : α) → (Σ' v : Value α, Inhab v (r.deriv c)) → (Σ' v : Value α, Inhab v r)
  | .char d, c, ⟨v, h⟩ => ⟨Value.char d, Inhab.char d⟩
  | .plus r₁ r₂, c, ⟨Value.left v₁, h₁⟩ =>
    have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_left h₁⟩
    ⟨v₁.left, h₁.left⟩
  | .plus r₁ r₂, c, ⟨Value.right v₂, h₂⟩ =>
    have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_right h₂⟩
    ⟨v₂.right, h₂.right⟩
  | .mul r₁ r₂, c, ⟨v, h⟩ => by
    rw [Regex.deriv] at h
    split_ifs at h with hn
    · match v with
      | Value.left (Value.seq v₁ v₂) =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst (inhab_left h)⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd (inhab_left h))⟩
      | Value.right (Value.seq v₁ v₂) =>
        have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_seq_snd (inhab_right h)⟩
        have h₁ := inhab_markEmpty (inhab_seq_fst (inhab_right h))
        exact ⟨v₁.seq v₂, h₁.seq h₂⟩
    · match v with
      | Value.seq v₁ v₂ =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst h⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd h)⟩
  | .star r, c, ⟨Value.seq v (Value.stars vs), h⟩ =>
    have ⟨v, hv⟩ := inj r c ⟨v, inhab_seq_fst h⟩
    ⟨Value.stars (v :: vs), Inhab.stars hv (inhab_seq_snd h)⟩
  | .group n s r, c, ⟨v, h⟩ =>
    have ⟨v, h⟩ := inj r c ⟨v, inhab_group h⟩
    ⟨v, Inhab.group h⟩

theorem inj_flat {r : Regex α} {c : α} {v : Value α} (hv : Inhab v (r.deriv c)) :
  (inj r c ⟨v, hv⟩).fst.flat = c::v.flat := by
  induction r generalizing v with
  | emptyset => nomatch hv
  | epsilon => nomatch hv
  | char d =>
    rw [deriv] at hv
    split_ifs at hv with hc
    · cases hv
      simp [inj, hc]
    · nomatch hv
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hv with
    | left hv =>
      simp [inj, ih₁]
    | right hv =>
      simp [inj, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [deriv] at hv
    split_ifs at hv with hn
    · match v with
      | Value.left (Value.seq v₁ v₂) =>
        simp [inj, hn, ih₁]
      | Value.right (Value.seq v₁ v₂) =>
        simp [inj, hn, ih₂]
        match hv with
        | Inhab.right (Inhab.seq hv₁ _) =>
          rw [inhab_markEmpty_flat hv₁]
          rfl
    · match v with
      | Value.seq v₁ v₂ =>
        simp [inj, hn, ih₁]
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj, ih]
  | group n s r ih =>
    simp [inj, ih]

def injs : (r : Regex α) → (s : List α) → (Σ' v : Value α, Inhab v (r.derivs s)) → (Σ' v' : Value α, Inhab v' r)
  | _, [], h => h
  | r, c::s, h => inj r c (injs (r.deriv c) s h)

def Regex.extract' : (r : Regex α) → (Σ' v : Value α, Inhab v r) → List (String × List α)
  | epsilon, _ => []
  | char _, _ => []
  | plus r₁ r₂, ⟨Value.left v₁, h₁⟩ =>
    r₁.extract' ⟨v₁, inhab_left h₁⟩
  | plus r₁ r₂, ⟨Value.right v₂, h₂⟩ =>
    r₂.extract' ⟨v₂, inhab_right h₂⟩
  | mul r₁ r₂, ⟨Value.seq v₁ v₂, h⟩ =>
    r₁.extract' ⟨v₁, inhab_seq_fst h⟩ ++ r₂.extract' ⟨v₂, inhab_seq_snd h⟩
  | star _, ⟨Value.stars [], _⟩ => []
  | star r, ⟨Value.stars (v::vs), h⟩ =>
    r.extract' ⟨v, inhab_stars_head h⟩ ++ (star r).extract' ⟨Value.stars vs, inhab_stars_tail h⟩
  | group n s r, ⟨v, h⟩ => (n, s ++ v.flat) :: r.extract' ⟨v, inhab_group h⟩

def Regex.captures' : Regex α → List α → List (String × List α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then r.extract' (injs r s (r'.mkeps h))
      else []

def Regex.parse : Regex α → List α → Option (Value α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then some (injs r s (r'.mkeps h)).fst
      else none

theorem parse_not_matches_iff {r : Regex α} (s : List α) :
  r.parse s = none ↔ ¬r.Matches s := by
  induction s generalizing r with
  | nil =>
    rw [←nullable_iff_matches_nil]
    simp [parse]
  | cons x xs ih =>
    rw [Matches_deriv, ←ih]
    simp [parse]

theorem parse_matches_iff {r : Regex α} (s : List α) :
  (r.parse s).isSome ↔ r.Matches s := by
  induction s generalizing r with
  | nil =>
    rw [←nullable_iff_matches_nil]
    simp [parse]
  | cons x xs ih =>
    rw [Matches_deriv, ←ih]
    simp [parse]
