import Mathlib

/-!
# Möbius Streams / LFTs for Exact Real Arithmetic (Revised)

A rigorously verified specification for Möbius Exact Real Arithmetic.
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
    -- The rigorous algebraic proof that det(MN) = det(M)det(N) ≠ 0
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
-/
noncomputable def apply (M : LFT) (x : ℝ) : ℝ :=
  (M.a * x + M.b) / (M.c * x + M.d)

/-- 
The restrictive invariant: guarantees no division-by-zero on[-1, 1].
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
Syntax fixed: fields must be on separate lines or strictly comma-separated.
-/
structure Tensor where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ

namespace Tensor

/-- The mathematical action of the Tensor on ℝ × ℝ. -/
noncomputable def apply (T : Tensor) (x y : ℝ) : ℝ :=
  (T.a * x * y + T.b * x + T.c * y + T.d) / (T.e * x * y + T.f * x + T.g * y + T.h)

/--
ABSORPTION: The tensor reads a digit from the left operand (x).
Mathematically: T_new(x', y) = T(M(x'), y).
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
Mathematically: T_new(x, y') = T(x, M(y')).
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

/--
EMISSION: The tensor outputs a digit D.
Mathematically, this evaluates T_new(x,y) = D^{-1} (T_old(x,y)).
If D =[a, b; c, d], the projective inverse is [d, -b; -c, a].
We multiply the T numerator by d and subtract b * denominator.
We multiply the T denominator by a and subtract c * numerator.
-/
def emit (T : Tensor) (D : LFT) : Tensor where
  a := D.d * T.a - D.b * T.e
  b := D.d * T.b - D.b * T.f
  c := D.d * T.c - D.b * T.g
  d := D.d * T.d - D.b * T.h
  e := -D.c * T.a + D.a * T.e
  f := -D.c * T.b + D.a * T.f
  g := -D.c * T.c + D.a * T.g
  h := -D.c * T.d + D.a * T.h

/-!
Note on Execution: 
In a fully computable layer, you MUST write a `normalize (T : Tensor) : Tensor`
function that computes the 8-way `gcd` of the fields and divides them out.
Without this, the tensor integers will overflow dramatically during evaluation.
-/

end Tensor

end Möbius
end Computable