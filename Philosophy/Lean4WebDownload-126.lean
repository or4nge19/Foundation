import Mathlib

/-!
# Möbius Streams / LFTs for Exact Real Arithmetic (Revised)

A rigorously verified specification for Möbius Exact Real Arithmetic.
We explicitly handle projective singularities to prevent false convergence.
-/

namespace Computable
namespace Möbius

/-- 
A Linear Fractional Transformation represented by a 2x2 integer matrix.
The determinant must be non-zero to ensure the map is non-singular.
-/
@[ext]
structure LFT where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det_neq_zero : a * d - b * c ≠ 0

namespace LFT

/-- The Identity LFT. -/
def id : LFT where
  a := 1; b := 0
  c := 0; d := 1
  det_neq_zero := by decide

/-- 
Composition of two LFTs (Matrix Multiplication). 
Matches function composition: (M.comp N) applied to x is M(N(x)).
-/
def comp (M N : LFT) : LFT where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d
  det_neq_zero := by
    -- Obsessive rigour: we prove the determinant multiplicative identity algebraically.
    have h : (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d) - 
             (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c) = 
             (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) := by ring
    intro h_zero
    rw [h] at h_zero
    cases mul_eq_zero.mp h_zero with
    | inl h1 => exact M.det_neq_zero h1
    | inr h2 => exact N.det_neq_zero h2

/-- 
The action of an LFT on ℝ. 
WARNING: In Lean, x / 0 = 0. This function is only topologically valid 
if we prove the denominator does not vanish on the domain of interest.
-/
noncomputable def apply (M : LFT) (x : ℝ) : ℝ :=
  (M.a * x + M.b) / (M.c * x + M.d)

/-- 
THE CRITICAL INVARIANT: 
An LFT has no pole on the interval [-1, 1] if |c| < |d|.
Proof sketch: For x ∈ [-1, 1], |cx| ≤ |c| < |d|, so cx + d ≠ 0.
This guarantees the LFT is strictly monotonic and continuous on the interval.
-/
def NoPoleOnBase (M : LFT) : Prop :=
  |M.c| < |M.d|

end LFT

/-!
## Standard Signed Digits as LFTs
Interval is [-1, 1].
-/

def digitNeg : LFT where
  a := 1; b := -1
  c := 0; d := 2
  det_neq_zero := by decide

def digitZero : LFT where
  a := 1; b := 0
  c := 0; d := 2
  det_neq_zero := by decide

def digitPos : LFT where
  a := 1; b := 1
  c := 0; d := 2
  det_neq_zero := by decide

abbrev LFTStream := ℕ → LFT

def partialComp (s : LFTStream) : ℕ → LFT
  | 0     => s 0
  | n + 1 => (partialComp s n).comp (s (n + 1))

/-!
## Valid Möbius Reals
-/

/-- 
A stream is contractive IF AND ONLY IF it contains no poles in the base interval,
and the width between the mapped endpoints approaches strictly 0.
Without `NoPoleOnBase`, checking the endpoints is mathematically meaningless.
-/
class IsContractive (s : LFTStream) : Prop where
  no_poles : ∀ n, (partialComp s n).NoPoleOnBase
  shrinks_to_zero : ∀ ε > 0, ∃ N, ∀ n ≥ N, 
    |LFT.apply (partialComp s n) 1 - LFT.apply (partialComp s n) (-1)| < ε

structure MöbiusReal where
  stream : LFTStream
  contractive : IsContractive stream

/-!
## Bilinear Fractional Transformations (Tensors)
T(x,y) = (axy + bx + cy + d) / (exy + fx + gy + h)
-/

/-- 
The core state of a binary operation (Addition, Multiplication, etc).
-/
structure Tensor where
  a : ℤ; b : ℤ; c : ℤ; d : ℤ
  e : ℤ; f : ℤ; g : ℤ; h : ℤ

namespace Tensor

/--
ABSORPTION: The tensor reads a digit from the left operand (x).
Mathematically, this is evaluating T(M(x'), y).
We substitute x = (A x' + B) / (C x' + D) into the tensor and clear denominators.
This is verified by collecting the xy, x, y, and 1 coefficients.
-/
def absorbX (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.c * M.c
  b := T.b * M.a + T.d * M.c
  c := T.a * M.b + T.c * M.d
  d := T.b * M.b + T.d * M.d
  e := T.e * M.a + T.g * M.c
  f := T.f * M.a + T.h * M.c
  g := T.e * M.b + T.g * M.d
  h := T.f * M.b + T.h * M.d

/--
ABSORPTION: The tensor reads a digit from the right operand (y).
Mathematically: T(x, M(y')).
-/
def absorbY (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.b * M.c
  b := T.a * M.b + T.b * M.d
  c := T.c * M.a + T.d * M.c
  d := T.c * M.b + T.d * M.d
  e := T.e * M.a + T.f * M.c
  f := T.e * M.b + T.f * M.d
  g := T.g * M.a + T.h * M.c
  h := T.g * M.b + T.h * M.d

end Tensor

end Möbius
end Computable