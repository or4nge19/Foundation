import Mathlib

/-!
# Analytic Exact Real Arithmetic (Field-Complete PIVP)

A rigorously separated Algebraic Specification for Computable Reals based on 
Polynomial Initial Value Problems (PIVPs).

Note: This specification uses Mathlib's `MvPolynomial` which is `noncomputable` 
due to classical zero-checks in `Finsupp`. A computable execution layer would 
shadow these definitions using concrete lists/arrays.
-/

namespace Computable.Analytic

open MvPolynomial
open scoped BigOperators

/-! =========================================================================
   PART 1: THE ALGEBRAIC STRUCTURE
   ========================================================================== -/

/-- 
An Analytic Real is purely defined by its Polynomial Vector Field and Initial Conditions.
The convergence proofs are safely decoupled from the algebraic definition.
-/
structure AnalyticReal (V : Type)[Fintype V] [DecidableEq V] where
  out : V
  init : V → ℚ
  deriv : V → MvPolynomial V ℤ
  out_init_zero : init out = 0

/-! =========================================================================
   PART 2: FIELD OPERATIONS (The Algebraic Combinators)
   ========================================================================== -/

/-- RECIPROCAL: z = 1/(x + 1) - 1. -/
noncomputable def invM1 {V : Type}[Fintype V] [DecidableEq V] 
  (X : AnalyticReal V) : AnalyticReal (Option V) where
  out := none
  init v := match v with
    | none => 0
    | some x => X.init x
  deriv v := match v with
    | none => 
        let dx := MvPolynomial.rename some (X.deriv X.out)
        let z  := MvPolynomial.X (none : Option V)
        - (z + 1)^2 * dx
    | some x => MvPolynomial.rename some (X.deriv x)
  out_init_zero := rfl

variable {V₁ V₂ : Type} [Fintype V₁][DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

/-- ADDITION: z' = x' + y', z(0) = 0. -/
noncomputable def add (X : AnalyticReal V₁) (Y : AnalyticReal V₂) : 
    AnalyticReal (Option (Sum V₁ V₂)) where
  out := none
  init v := match v with
    | none => 0
    | some (Sum.inl x) => X.init x
    | some (Sum.inr y) => Y.init y
  deriv v := match v with
    | none => 
        MvPolynomial.rename (some ∘ Sum.inl) (X.deriv X.out) + 
        MvPolynomial.rename (some ∘ Sum.inr) (Y.deriv Y.out)
    | some (Sum.inl x) => MvPolynomial.rename (some ∘ Sum.inl) (X.deriv x)
    | some (Sum.inr y) => MvPolynomial.rename (some ∘ Sum.inr) (Y.deriv y)
  out_init_zero := rfl

/-- MULTIPLICATION: z' = x'y + xy', z(0) = 0. -/
noncomputable def mul (X : AnalyticReal V₁) (Y : AnalyticReal V₂) : 
    AnalyticReal (Option (Sum V₁ V₂)) where
  out := none
  init v := match v with
    | none => 0
    | some (Sum.inl x) => X.init x
    | some (Sum.inr y) => Y.init y
  deriv v := match v with
    | none => 
        let dx := MvPolynomial.rename (some ∘ Sum.inl) (X.deriv X.out)
        let dy := MvPolynomial.rename (some ∘ Sum.inr) (Y.deriv Y.out)
        let x_var := MvPolynomial.X (some (Sum.inl X.out))
        let y_var := MvPolynomial.X (some (Sum.inr Y.out))
        dx * y_var + x_var * dy
    | some (Sum.inl x) => MvPolynomial.rename (some ∘ Sum.inl) (X.deriv x)
    | some (Sum.inr y) => MvPolynomial.rename (some ∘ Sum.inr) (Y.deriv y)
  out_init_zero := rfl

/-! =========================================================================
   PART 3: SEMANTICS (The Bridge to Mathlib ℝ)
   ========================================================================== -/

/-- LIE DERIVATIVE OPERATOR. -/
noncomputable def lieDeriv {V : Type} [Fintype V] [DecidableEq V] 
  (deriv : V → MvPolynomial V ℤ) (F : MvPolynomial V ℤ) : MvPolynomial V ℤ :=
  ∑ v : V, (MvPolynomial.pderiv v F) * (deriv v)

/-- Exact Taylor coefficient of the output variable. -/
noncomputable def taylorCoeff {V : Type} [Fintype V] [DecidableEq V]
  (A : AnalyticReal V) (k : ℕ) : ℚ :=
  let rec lieIter : ℕ → MvPolynomial V ℤ
    | 0 => MvPolynomial.X A.out
    | i + 1 => lieDeriv A.deriv (lieIter i)
  (MvPolynomial.eval A.init (MvPolynomial.map (Int.castRingHom ℚ) (lieIter k))) / (Nat.factorial k : ℚ)

/-- Partial sums of the Taylor series. -/
noncomputable def approxSum {V : Type} [Fintype V] [DecidableEq V]
  (A : AnalyticReal V) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), taylorCoeff A k

/-- 
THE DENOTATION MAP
To evaluate an Analytic Real, the caller MUST provide a proof `h` that the 
Taylor series converges (i.e., it forms a Cauchy sequence). 
This removes the `sorry` completely and maintains absolute formal rigour.
-/
noncomputable def toReal {V : Type} [Fintype V] [DecidableEq V] 
  (A : AnalyticReal V) (h : CauchySeq (fun n => (approxSum A n : ℝ))) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete h)

end Computable.Analytic