import Mathlib

/-!
# Propositional Logic: Minimal, Intuitionistic, and Classical

This module implements the syntactic foundations of propositional logic, 
parameterized by the logical system (Minimal, Intuitionistic, Classical). 

The formalization closely follows Sergio Galvan's "Non Contraddizione e Terzo Escluso".
In particular, it captures Galvan's comparative analysis of the negation connective:
- Minimal logic (`j`) provides the principle of refutation of contradictory hypotheses.
- Intuitionistic logic (`i`) adds `ex falso quodlibet` (Pseudo-Scotus), banishing 
  any incoherent theory by inferring the totality of formulas.
- Classical logic (`k`) is defined strictly by classical reductio ad absurdum, from 
  which both the intuitionistic rules and classical double negation can be derived.
-/

namespace Galvan.Logic.Propositional

/-- 
Propositional formulas parameterized by a type of atoms `α`.
-/
inductive Formula (α : Type u)
| atom (a : α)
| and (φ ψ : Formula α)
| or (φ ψ : Formula α)
| imp (φ ψ : Formula α)
| neg (φ : Formula α)
deriving DecidableEq, Repr, Inhabited

-- Mathlib-idiomatic scoped notations for the object language
scoped infixr:75 " ⋏ " => Formula.and
scoped infixr:70 " ⋎ " => Formula.or
scoped infixr:60 " ⟶ " => Formula.imp
scoped prefix:80 "~"   => Formula.neg

/-- 
The three systems of logic analyzed by Galvan (p. 18):
- `minimal` (`j`)
- `intuitionistic` (`i`)
- `classical` (`k`)
-/
inductive LogicType
| minimal
| intuitionistic
| classical
deriving DecidableEq, Repr, Inhabited

open LogicType

/-- 
The finitary derivation relation `Γ ⊢[sys] φ`.
The context `Γ` is defined as a `List` of formulas to assure finitary proofs, 
aligning with `mathlib`'s structural proof theory principles.
-/
inductive Derivable {α : Type u} (sys : LogicType) : List (Formula α) → Formula α → Prop
-- Structural / Base Connective Rules (Common to all systems)
| ax {Γ φ} : φ ∈ Γ → Derivable sys Γ φ
| and_intro {Γ φ ψ} : Derivable sys Γ φ → Derivable sys Γ ψ → Derivable sys Γ (φ ⋏ ψ)
| and_elim_l {Γ φ ψ} : Derivable sys Γ (φ ⋏ ψ) → Derivable sys Γ φ
| and_elim_r {Γ φ ψ} : Derivable sys Γ (φ ⋏ ψ) → Derivable sys Γ ψ
| or_intro_l {Γ φ ψ} : Derivable sys Γ φ → Derivable sys Γ (φ ⋎ ψ)
| or_intro_r {Γ φ ψ} : Derivable sys Γ ψ → Derivable sys Γ (φ ⋎ ψ)
| or_elim {Γ φ ψ χ} : Derivable sys Γ (φ ⋎ ψ) → Derivable sys (φ :: Γ) χ → Derivable sys (ψ :: Γ) χ → Derivable sys Γ χ
| imp_intro {Γ φ ψ} : Derivable sys (φ :: Γ) ψ → Derivable sys Γ (φ ⟶ ψ)
| imp_elim {Γ φ ψ} : Derivable sys Γ (φ ⟶ ψ) → Derivable sys Γ φ → Derivable sys Γ ψ

-- Negation Rules (Galvan p. 18)
-- Minimal negation (¬j): Primitive in minimal and intuitionistic logic.
| neg_j {Γ φ ψ} : (sys = minimal ∨ sys = intuitionistic) → 
    Derivable sys (φ :: Γ) ψ → Derivable sys (φ :: Γ) (~ψ) → Derivable sys Γ (~φ)
-- Intuitionistic negation (¬i) / Pseudo-Scotus: Primitive only in intuitionistic logic.
| neg_i {Γ φ ψ} : sys = intuitionistic → 
    Derivable sys Γ φ → Derivable sys Γ (~φ) → Derivable sys Γ ψ
-- Classical negation (¬k): Primitive only in classical logic.
| neg_k {Γ φ ψ} : sys = classical → 
    Derivable sys (~φ :: Γ) ψ → Derivable sys (~φ :: Γ) (~ψ) → Derivable sys Γ φ

scoped notation:50 Γ " ⊢[" sys "] " φ => Derivable sys Γ φ

/--
Entailment from an arbitrary set of formulas.
Defined as the existence of a finite list from which the formula is derivable.
This establishes compactness by definition.
-/
def SetDerivable {α : Type u} (sys : LogicType) (Γ : Set (Formula α)) (φ : Formula α) : Prop :=
  ∃ Γ0 : List (Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) ∧ Γ0 ⊢[sys] φ

scoped notation:50 Γ " ⊢s[" sys "] " φ => SetDerivable sys Γ φ

-- -------------------------------------------------------------------------
-- Structural Meta-Theorems
-- -------------------------------------------------------------------------

/-- 
Weakening: Adding unused formulas to the context does not invalidate a derivation.
In this setup, weakening implies permutation because `List.Subset` ignores order.
-/
theorem weakening {α : Type u} {sys : LogicType} {Γ Δ : List (Formula α)} {φ : Formula α}
  (h : Γ ⊢[sys] φ) (hsub : Γ ⊆ Δ) : Δ ⊢[sys] φ := by
  induction h generalizing Δ with
  | ax h_in => exact .ax (hsub h_in)
  | and_intro _ _ ih1 ih2 => exact .and_intro (ih1 hsub) (ih2 hsub)
  | and_elim_l _ ih => exact .and_elim_l (ih hsub)
  | and_elim_r _ ih => exact .and_elim_r (ih hsub)
  | or_intro_l _ ih => exact .or_intro_l (ih hsub)
  | or_intro_r _ ih => exact .or_intro_r (ih hsub)
  | or_elim _ _ _ ih1 ih2 ih3 =>
    exact .or_elim (ih1 hsub)
      (ih2 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
      (ih3 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
  | imp_intro _ ih =>
    exact .imp_intro (ih (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
  | imp_elim _ _ ih1 ih2 => exact .imp_elim (ih1 hsub) (ih2 hsub)
  | neg_j hsys _ _ ih1 ih2 =>
    exact .neg_j hsys
      (ih1 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
      (ih2 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
  | neg_i hsys _ _ ih1 ih2 => exact .neg_i hsys (ih1 hsub) (ih2 hsub)
  | neg_k hsys _ _ ih1 ih2 =>
    exact .neg_k hsys
      (ih1 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))
      (ih2 (fun _ hx => match hx with | .head _ => .head _ | .tail _ hx => .tail _ (hsub hx)))

/-- 
Generalized Cut (Multi-Cut): If `ψ` is derivable from `Δ`, and every formula in `Δ` 
is derivable from `Γ`, then `ψ` is derivable from `Γ`.
-/
theorem cut_gen {α : Type u} {sys : LogicType} {Δ : List (Formula α)} {ψ : Formula α}
  (h : Δ ⊢[sys] ψ) {Γ : List (Formula α)} (hΓ : ∀ χ ∈ Δ, Γ ⊢[sys] χ) : Γ ⊢[sys] ψ := by
  induction h generalizing Γ with
  | ax h_in => exact hΓ _ h_in
  | and_intro _ _ ih1 ih2 => exact .and_intro (ih1 hΓ) (ih2 hΓ)
  | and_elim_l _ ih => exact .and_elim_l (ih hΓ)
  | and_elim_r _ ih => exact .and_elim_r (ih hΓ)
  | or_intro_l _ ih => exact .or_intro_l (ih hΓ)
  | or_intro_r _ ih => exact .or_intro_r (ih hΓ)
  | or_elim _ _ _ ih1 ih2 ih3 =>
    exact .or_elim (ih1 hΓ)
      (ih2 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
      (ih3 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
  | imp_intro _ ih =>
    exact .imp_intro (ih (fun χ hχ => match hχ with
      | .head _ => .ax (.head _)
      | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
  | imp_elim _ _ ih1 ih2 => exact .imp_elim (ih1 hΓ) (ih2 hΓ)
  | neg_j hsys _ _ ih1 ih2 =>
    exact .neg_j hsys
      (ih1 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
      (ih2 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
  | neg_i hsys _ _ ih1 ih2 => exact .neg_i hsys (ih1 hΓ) (ih2 hΓ)
  | neg_k hsys _ _ ih1 ih2 =>
    exact .neg_k hsys
      (ih1 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))
      (ih2 (fun χ hχ => match hχ with
        | .head _ => .ax (.head _)
        | .tail _ h_tail => weakening (hΓ _ h_tail) (fun _ hx => .tail _ hx)))

/-- 
Standard Cut Rule / Transitivity.
-/
theorem cut {α : Type u} {sys : LogicType} {Γ : List (Formula α)} {φ ψ : Formula α}
  (hφ : Γ ⊢[sys] φ) (hψ : (φ :: Γ) ⊢[sys] ψ) : Γ ⊢[sys] ψ := by
  apply cut_gen hψ
  intro χ hχ
  cases hχ with
  | head => exact hφ
  | tail _ h_in_Γ => exact .ax h_in_Γ


-- -------------------------------------------------------------------------
-- Meta-Theorems on Negation (Galvan pp. 19-23)
-- -------------------------------------------------------------------------

/-- 
Classical Double Negation Elimination (`DNc`). (Galvan p. 21)
Derived purely using the primitive classical negation rule (`neg_k`).
-/
theorem DNc {α} {Γ : List (Formula α)} {φ : Formula α} (h : Γ ⊢[.classical] (~~φ)) : Γ ⊢[.classical] φ := by
  apply Derivable.neg_k rfl (ψ := ~φ)
  · exact .ax (.head _)
  · exact weakening h (fun _ hx => .tail _ hx)

/-- 
The minimal negation rule (`neg_j`) is derivable natively in Classical Logic. (Galvan p. 21)
Proof heavily leverages `DNc` and Cut.
-/
theorem neg_j_classical {α} {Γ : List (Formula α)} {φ ψ : Formula α}
  (h1 : (φ :: Γ) ⊢[.classical] ψ) (h2 : (φ :: Γ) ⊢[.classical] (~ψ)) : Γ ⊢[.classical] (~φ) := by
  apply Derivable.neg_k rfl (ψ := ψ)
  · apply cut_gen h1
    intro χ hχ
    cases hχ with
    | head => exact DNc (.ax (.head _))
    | tail _ h_tail => exact .ax (.tail _ h_tail)
  · apply cut_gen h2
    intro χ hχ
    cases hχ with
    | head => exact DNc (.ax (.head _))
    | tail _ h_tail => exact .ax (.tail _ h_tail)

/-- 
The intuitionistic negation rule (`neg_i`) is derivable natively in Classical Logic. (Galvan p. 20)
-/
theorem neg_i_classical {α} {Γ : List (Formula α)} {φ ψ : Formula α}
  (h1 : Γ ⊢[.classical] φ) (h2 : Γ ⊢[.classical] (~φ)) : Γ ⊢[.classical] ψ := by
  apply Derivable.neg_k rfl (ψ := φ)
  · exact weakening h1 (fun _ hx => .tail _ hx)
  · exact weakening h2 (fun _ hx => .tail _ hx)

/-- 
Rule of Autocontradiction (AC). Valid across all three logics. (Galvan p. 23)
If `~φ` is derivable under the assumption of `φ`, then `~φ` is unconditionally derivable.
-/
theorem autocontradiction {α} {sys : LogicType} {Γ : List (Formula α)} {φ : Formula α}
  (h : (φ :: Γ) ⊢[sys] (~φ)) : Γ ⊢[sys] (~φ) := by
  cases sys with
  | minimal        => exact .neg_j (Or.inl rfl) (.ax (.head _)) h
  | intuitionistic => exact .neg_j (Or.inr rfl) (.ax (.head _)) h
  | classical      => exact neg_j_classical (.ax (.head _)) h

/-- 
Rule of Autofondazione (AF). Valid strictly in Classical logic. (Galvan p. 23)
If `φ` is derivable under the assumption of `~φ`, then `φ` is unconditionally derivable.
The derivation uses the `neg_k` rule crucially, attesting to its philosophical relevance.
-/
theorem autofondazione {α} {Γ : List (Formula α)} {φ : Formula α}
  (h : (~φ :: Γ) ⊢[.classical] φ) : Γ ⊢[.classical] φ :=
  .neg_k rfl h (.ax (.head _))

end Galvan.Logic.Propositional