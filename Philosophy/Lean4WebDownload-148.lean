import Mathlib.Data.Set.Defs
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


import Mathlib.Data.Set.Defs
import Mathlib.Order.UpperLower.Basic

/-!
# Propositional Logic: Minimal, Intuitionistic, and Classical (Syntax & Semantics)

This module formalizes both the syntactic derivation calculi (PR 1) and the Kripke 
semantics (PR 2) for propositional logic as outlined in Chapters 1-3 of Sergio 
Galvan's "Non Contraddizione e Terzo Escluso".

## Architectural Design for Semantics
To align with `mathlib`'s principles of modularity and order theory:
- We use a single `Preorder W` to represent Kripke worlds.
- A valuation assigns to each atom an `UpperSet W` (a monotone upward-closed subset).
- **Minimal logic** introduces the notion of "normal" and "non-normal" worlds. We model 
  this by passing a designated `Norm : UpperSet W`. In non-normal worlds, contradictions 
  do not trivialize the theory.
- **Intuitionistic logic** is simply the special case where `Norm = ⊤` (all worlds are normal).
- **Classical logic** is the special case where `Norm = ⊤` and the preorder is discrete 
  (meaning `w ≤ v → w = v`), collapsing the semantics into standard Boolean logic.
-/

namespace Galvan.Logic.Propositional

-- -------------------------------------------------------------------------
-- Syntax and Derivability (From PR 1)
-- -------------------------------------------------------------------------

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

/-- The three systems of logic analyzed by Galvan. -/
inductive LogicType | minimal | intuitionistic | classical
deriving DecidableEq, Repr, Inhabited

open LogicType

/-- The finitary derivation relation `Γ ⊢[sys] φ`. -/
inductive Derivable {α : Type u} (sys : LogicType) : List (Formula α) → Formula α → Prop
| ax {Γ φ} : φ ∈ Γ → Derivable sys Γ φ
| and_intro {Γ φ ψ} : Derivable sys Γ φ → Derivable sys Γ ψ → Derivable sys Γ (φ ⋏ ψ)
| and_elim_l {Γ φ ψ} : Derivable sys Γ (φ ⋏ ψ) → Derivable sys Γ φ
| and_elim_r {Γ φ ψ} : Derivable sys Γ (φ ⋏ ψ) → Derivable sys Γ ψ
| or_intro_l {Γ φ ψ} : Derivable sys Γ φ → Derivable sys Γ (φ ⋎ ψ)
| or_intro_r {Γ φ ψ} : Derivable sys Γ ψ → Derivable sys Γ (φ ⋎ ψ)
| or_elim {Γ φ ψ χ} : Derivable sys Γ (φ ⋎ ψ) → Derivable sys (φ :: Γ) χ → Derivable sys (ψ :: Γ) χ → Derivable sys Γ χ
| imp_intro {Γ φ ψ} : Derivable sys (φ :: Γ) ψ → Derivable sys Γ (φ ⟶ ψ)
| imp_elim {Γ φ ψ} : Derivable sys Γ (φ ⟶ ψ) → Derivable sys Γ φ → Derivable sys Γ ψ
-- Negation Rules
| neg_j {Γ φ ψ} : (sys = minimal ∨ sys = intuitionistic) → 
    Derivable sys (φ :: Γ) ψ → Derivable sys (φ :: Γ) (~ψ) → Derivable sys Γ (~φ)
| neg_i {Γ φ ψ} : sys = intuitionistic → 
    Derivable sys Γ φ → Derivable sys Γ (~φ) → Derivable sys Γ ψ
| neg_k {Γ φ ψ} : sys = classical → 
    Derivable sys (~φ :: Γ) ψ → Derivable sys (~φ :: Γ) (~ψ) → Derivable sys Γ φ

scoped notation:50 Γ " ⊢[" sys "] " φ => Derivable sys Γ φ


-- -------------------------------------------------------------------------
-- Kripke Semantics (PR 2)
-- -------------------------------------------------------------------------

/-- 
The generalized forcing relation `⊨` for Minimal Kripke frames.
`Norm` specifies the upward-closed set of normal worlds.
-/
def Forces {α W : Type u}[Preorder W] (Norm : UpperSet W) (V : α → UpperSet W) : Formula α → W → Prop
| .atom a, w   => w ∈ V a
| .and φ ψ, w  => Forces Norm V φ w ∧ Forces Norm V ψ w
| .or φ ψ, w   => Forces Norm V φ w ∨ Forces Norm V ψ w
| .imp φ ψ, w  => ∀ v, w ≤ v → Forces Norm V φ v → Forces Norm V ψ v
| .neg φ, w    => ∀ v, w ≤ v → v ∈ Norm → ¬ Forces Norm V φ v

/-- 
Monotonicity Lemma (Galvan Ch. 2 & 3): 
If a formula is forced at `w`, it remains forced at all accessible worlds `v ≥ w`.
Proof proceeds by structural induction on the formula `φ`.
-/
theorem forces_monotone {α W : Type u} [Preorder W] (Norm : UpperSet W) (V : α → UpperSet W)
  (φ : Formula α) {w v : W} (hwv : w ≤ v) (h : Forces Norm V φ w) : Forces Norm V φ v := by
  induction φ generalizing w v with
  | atom a => exact (V a).upper' hwv h
  | and φ ψ ih1 ih2 => exact ⟨ih1 hwv h.1, ih2 hwv h.2⟩
  | or φ ψ ih1 ih2 => 
    cases h with
    | inl h1 => exact Or.inl (ih1 hwv h1)
    | inr h2 => exact Or.inr (ih2 hwv h2)
  | imp φ ψ _ _ =>
    intro u hvu hu
    exact h u (le_trans hwv hvu) hu
  | neg φ _ =>
    intro u hvu hu
    exact h u (le_trans hwv hvu) hu

/--
Evaluates the required Kripke frame conditions depending on the system's strength.
-/
def MeetsCondition (sys : LogicType) {W : Type u} [Preorder W] (Norm : UpperSet W) : Prop :=
  match sys with
  | .minimal => True
  | .intuitionistic => Norm = ⊤
  | .classical => Norm = ⊤ ∧ ∀ w v : W, w ≤ v → w = v

/-- Semantic entailment across the unified frame constraints. -/
def SemanticEntails {α : Type u} (sys : LogicType) (Γ : List (Formula α)) (φ : Formula α) : Prop :=
  ∀ (W : Type u)[Preorder W] (Norm : UpperSet W) (V : α → UpperSet W),
    MeetsCondition sys Norm →
    ∀ w : W, (∀ ψ ∈ Γ, Forces Norm V ψ w) → Forces Norm V φ w


-- -------------------------------------------------------------------------
-- Soundness Meta-Theorem
-- -------------------------------------------------------------------------

/-- 
Soundness Theorem: If `Γ ⊢[sys] φ`, then `Γ ⊨[sys] φ`.
This elegantly captures the soundness of all three logics in a single inductive sweep. 
-/
theorem soundness {α : Type u} {sys : LogicType} {Γ : List (Formula α)} {φ : Formula α}
  (h : Γ ⊢[sys] φ) : SemanticEntails sys Γ φ := by
  intro W _ Norm V hsys w hΓ
  induction h generalizing w with
  | ax h_in => 
    exact hΓ _ h_in
  
  | and_intro _ _ ih1 ih2 => 
    exact ⟨ih1 w hΓ, ih2 w hΓ⟩
  
  | and_elim_l _ ih => 
    exact (ih w hΓ).1
  
  | and_elim_r _ ih => 
    exact (ih w hΓ).2
  
  | or_intro_l _ ih => 
    exact Or.inl (ih w hΓ)
  
  | or_intro_r _ ih => 
    exact Or.inr (ih w hΓ)
  
  | or_elim _ _ _ ih1 ih2 ih3 =>
    cases ih1 w hΓ with
    | inl hφ =>
      apply ih2 w
      intro χ hχ
      cases hχ with
      | head => exact hφ
      | tail _ h_tail => exact hΓ _ h_tail
    | inr hψ =>
      apply ih3 w
      intro χ hχ
      cases hχ with
      | head => exact hψ
      | tail _ h_tail => exact hΓ _ h_tail
  
  | imp_intro _ ih =>
    intro v hwv hφ
    apply ih v
    intro χ hχ
    cases hχ with
    | head => exact hφ
    | tail _ h_tail => exact forces_monotone Norm V _ hwv (hΓ _ h_tail)
  
  | imp_elim _ _ ih1 ih2 =>
    exact ih1 w hΓ w (le_refl w) (ih2 w hΓ)
  
  | neg_j h_sys _ _ ih1 ih2 =>
    intro v hwv h_norm hφ
    -- Create the new context evaluation function implicitly matching the extended list
    have h_ctx (χ : Formula α) (hχ : χ ∈ _) : Forces Norm V χ v := by
      cases hχ with
      | head => exact hφ
      | tail _ h_tail => exact forces_monotone Norm V χ hwv (hΓ χ h_tail)
    
    have h_psi := ih1 v h_ctx
    have h_not_psi := ih2 v h_ctx
    exact h_not_psi v (le_refl v) h_norm h_psi
  
  | neg_i h_sys _ _ ih1 ih2 =>
    subst h_sys
    have h_norm_top : Norm = ⊤ := hsys
    have h_not_phi := ih2 w hΓ
    have h_phi := ih1 w hΓ
    have w_in_norm : w ∈ Norm := by
      rw [h_norm_top]
      exact Set.mem_univ w
    exact False.elim (h_not_phi w (le_refl w) w_in_norm h_phi)
  
  | neg_k h_sys _ _ ih1 ih2 =>
    subst h_sys
    rcases hsys with ⟨h_norm_top, h_discrete⟩
    open Classical in
    by_contra h_not_phi
    
    have h_ctx (χ : Formula α) (hχ : χ ∈ _) : Forces Norm V χ w := by
      cases hχ with
      | head => 
        -- `head` guarantees `χ` is the negation we are refuting
        intro v hwv _
        have hwv_eq : w = v := h_discrete w v hwv
        subst hwv_eq
        exact h_not_phi
      | tail _ h_tail => exact hΓ χ h_tail
      
    have h_psi := ih1 w h_ctx
    have h_not_psi := ih2 w h_ctx
    have w_in_norm : w ∈ Norm := by
      rw [h_norm_top]
      exact Set.mem_univ w
      
    exact h_not_psi w (le_refl w) w_in_norm h_psi

end Galvan.Logic.Propositional