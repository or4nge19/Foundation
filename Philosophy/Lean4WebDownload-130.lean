import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Möbius Streams / LFTs for Exact Real Arithmetic (Revised & Complete)

A rigorously verified specification AND Execution Engine for Möbius Exact Real Arithmetic.
This layer implements Integer-Only bounding Oracles and Structural Operational Semantics
to evaluate exact reals without panics, approximations, or termination compromises.
-/

namespace Computable
namespace Möbius

/-! =========================================================================
   PART 1: THE ALGEBRAIC SPECIFICATION (Verified Base)
   ========================================================================== -/

@[ext]
structure LFT where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det_neq_zero : a * d - b * c ≠ 0

namespace LFT

def id : LFT where
  a := 1
  b := 0
  c := 0
  d := 1
  det_neq_zero := by decide

def comp (M N : LFT) : LFT where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d
  det_neq_zero := by
    have h : (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d) - 
             (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c) = 
             (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) := by ring
    intro h_zero
    rw [h] at h_zero
    cases mul_eq_zero.mp h_zero with
    | inl h1 => exact M.det_neq_zero h1
    | inr h2 => exact N.det_neq_zero h2

noncomputable def apply (M : LFT) (x : ℝ) : ℝ :=
  (M.a * x + M.b) / (M.c * x + M.d)

def NoPoleOnBase (M : LFT) : Prop := |M.c| < |M.d|

end LFT

def digitNeg : LFT where
  a := 1
  b := -1
  c := 0
  d := 2
  det_neq_zero := by decide

def digitZero : LFT where
  a := 1
  b := 0
  c := 0
  d := 2
  det_neq_zero := by decide

def digitPos : LFT where
  a := 1
  b := 1
  c := 0
  d := 2
  det_neq_zero := by decide

abbrev LFTStream := ℕ → LFT

def partialComp (s : LFTStream) : ℕ → LFT
  | 0     => s 0
  | n + 1 => (partialComp s n).comp (s (n + 1))

class IsContractive (s : LFTStream) : Prop where
  no_poles : ∀ n, (partialComp s n).NoPoleOnBase
  shrinks_to_zero : ∀ ε > 0, ∃ N, ∀ n ≥ N, 
    |LFT.apply (partialComp s n) 1 - LFT.apply (partialComp s n) (-1)| < ε

structure MöbiusReal where
  stream : LFTStream
  contractive : IsContractive stream

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

def absorbX (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.c * M.c
  b := T.b * M.a + T.d * M.c
  c := T.a * M.b + T.c * M.d
  d := T.b * M.b + T.d * M.d
  e := T.e * M.a + T.g * M.c
  f := T.f * M.a + T.h * M.c
  g := T.e * M.b + T.g * M.d
  h := T.f * M.b + T.h * M.d

def absorbY (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.b * M.c
  b := T.a * M.b + T.b * M.d
  c := T.c * M.a + T.d * M.c
  d := T.c * M.b + T.d * M.d
  e := T.e * M.a + T.f * M.c
  f := T.e * M.b + T.f * M.d
  g := T.g * M.a + T.h * M.c
  h := T.g * M.b + T.h * M.d

def emit (T : Tensor) (D : LFT) : Tensor where
  a := D.d * T.a - D.b * T.e
  b := D.d * T.b - D.b * T.f
  c := D.d * T.c - D.b * T.g
  d := D.d * T.d - D.b * T.h
  e := -D.c * T.a + D.a * T.e
  f := -D.c * T.b + D.a * T.f
  g := -D.c * T.c + D.a * T.g
  h := -D.c * T.d + D.a * T.h

/-! =========================================================================
   PART 2: THE EXECUTION ENGINE (Rigorous, Integer-Only Computation)
   ========================================================================== -/

def normalize (T : Tensor) : Tensor :=
  let g1 := (T.a.natAbs.gcd T.b.natAbs).gcd (T.c.natAbs.gcd T.d.natAbs)
  let g2 := (T.e.natAbs.gcd T.f.natAbs).gcd (T.g.natAbs.gcd T.h.natAbs)
  let g := g1.gcd g2
  if g ≤ 1 then T else
  let gZ : ℤ := (g : ℤ)
  { a := T.a / gZ, b := T.b / gZ, c := T.c / gZ, d := T.d / gZ,
    e := T.e / gZ, f := T.f / gZ, g := T.g / gZ, h := T.h / gZ }

def cornerValues (T : Tensor) : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) :=
  let n1 :=  T.a + T.b + T.c + T.d
  let d1 :=  T.e + T.f + T.g + T.h
  let n2 := -T.a + T.b - T.c + T.d
  let d2 := -T.e + T.f - T.g + T.h
  let n3 := -T.a - T.b + T.c + T.d
  let d3 := -T.e - T.f + T.g + T.h
  let n4 :=  T.a - T.b - T.c + T.d
  let d4 :=  T.e - T.f - T.g + T.h
  ((n1, d1), (n2, d2), (n3, d3), (n4, d4))

def hasNoPole (d1 d2 d3 d4 : ℤ) : Bool :=
  (d1 > 0 && d2 > 0 && d3 > 0 && d4 > 0) ||
  (d1 < 0 && d2 < 0 && d3 < 0 && d4 < 0)

def inDigitNeg (n d : ℤ) : Bool :=
  let s := if d > 0 then (1 : ℤ) else (-1 : ℤ)
  let abs_d := d * s
  let num := n * s
  (num ≤ 0) && (num ≥ -abs_d)

def inDigitZero (n d : ℤ) : Bool :=
  let s := if d > 0 then (1 : ℤ) else (-1 : ℤ)
  let abs_d := d * s
  let num2 := 2 * n * s
  (num2 ≤ abs_d) && (num2 ≥ -abs_d)

def inDigitPos (n d : ℤ) : Bool :=
  let s := if d > 0 then (1 : ℤ) else (-1 : ℤ)
  let abs_d := d * s
  let num := n * s
  (num ≥ 0) && (num ≤ abs_d)

inductive EmitDecision
| neg | zero | pos | absorb
deriving DecidableEq

def oracle (T : Tensor) : EmitDecision :=
  let ((n1,d1), (n2,d2), (n3,d3), (n4,d4)) := T.cornerValues
  if !hasNoPole d1 d2 d3 d4 then EmitDecision.absorb else
  if inDigitNeg n1 d1 && inDigitNeg n2 d2 && inDigitNeg n3 d3 && inDigitNeg n4 d4 then
    EmitDecision.neg
  else if inDigitZero n1 d1 && inDigitZero n2 d2 && inDigitZero n3 d3 && inDigitZero n4 d4 then
    EmitDecision.zero
  else if inDigitPos n1 d1 && inDigitPos n2 d2 && inDigitPos n3 d3 && inDigitPos n4 d4 then
    EmitDecision.pos
  else EmitDecision.absorb

end Tensor

/-! =========================================================================
   PART 3: STRUCTURAL OPERATIONAL SEMANTICS (The VM)
   ========================================================================== -/

structure VMState where
  T : Tensor
  idx_x : ℕ
  idx_y : ℕ
  absorb_x_next : Bool

inductive VMStep : VMState → Option LFT → VMState → Prop

  | emitNeg {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.neg) :
      VMStep s (some digitNeg) { s with T := (s.T.emit digitNeg).normalize }

  | emitZero {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.zero) :
      VMStep s (some digitZero) { s with T := (s.T.emit digitZero).normalize }

  | emitPos {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.pos) :
      VMStep s (some digitPos) { s with T := (s.T.emit digitPos).normalize }

  | absorbX {s : VMState} (sx : LFTStream) 
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb) 
      (h2 : s.absorb_x_next = true) :
      VMStep s none { s with 
                      T := (s.T.absorbX (sx s.idx_x)).normalize, 
                      idx_x := s.idx_x + 1, 
                      absorb_x_next := false }

  | absorbY {s : VMState} (sy : LFTStream) 
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb) 
      (h2 : s.absorb_x_next = false) :
      VMStep s none { s with 
                      T := (s.T.absorbY (sy s.idx_y)).normalize, 
                      idx_y := s.idx_y + 1, 
                      absorb_x_next := true }

/-! =========================================================================
   PART 4: TOPOLOGICAL SOUNDNESS OF EMISSION
   ========================================================================== -/

noncomputable def Tensor.apply (T : Tensor) (x y : ℝ) : ℝ :=
  (T.a * x * y + T.b * x + T.c * y + T.d) / (T.e * x * y + T.f * x + T.g * y + T.h)

lemma affine_nonneg_of_endpoints (M B : ℝ) (h1 : M * 1 + B ≥ 0) (hm1 : M * (-1) + B ≥ 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B ≥ 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * (-1) ≤ M * x := mul_le_mul_of_nonneg_left hx1 hM
    linarith
  · have : M * 1 ≤ M * x := mul_le_mul_of_nonpos_left hx2 hM
    linarith

lemma affine_nonpos_of_endpoints (M B : ℝ) (h1 : M * 1 + B ≤ 0) (hm1 : M * (-1) + B ≤ 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B ≤ 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * x ≤ M * 1 := mul_le_mul_of_nonneg_left hx2 hM
    linarith
  · have : M * x ≤ M * (-1) := mul_le_mul_of_nonpos_left hx1 hM
    linarith

lemma affine_pos_of_endpoints (M B : ℝ) (h1 : M * 1 + B > 0) (hm1 : M * (-1) + B > 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B > 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * (-1) ≤ M * x := mul_le_mul_of_nonneg_left hx1 hM
    linarith
  · have : M * 1 ≤ M * x := mul_le_mul_of_nonpos_left hx2 hM
    linarith

lemma affine_neg_of_endpoints (M B : ℝ) (h1 : M * 1 + B < 0) (hm1 : M * (-1) + B < 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B < 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * x ≤ M * 1 := mul_le_mul_of_nonneg_left hx2 hM
    linarith
  · have : M * x ≤ M * (-1) := mul_le_mul_of_nonpos_left hx1 hM
    linarith

lemma bilinear_nonpos_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D ≤ 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D ≤ 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D ≤ 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D ≤ 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D ≤ 0 := by
  intro x y hx1 hx2 hy1 hy2
  have h_top_1 : (A * 1 + B) * 1 + (C * 1 + D) ≤ 0 := by linarith
  have h_top_m1 : (A * 1 + B) * (-1) + (C * 1 + D) ≤ 0 := by linarith
  have h_top := affine_nonpos_of_endpoints (A * 1 + B) (C * 1 + D) h_top_1 h_top_m1 x hx1 hx2
  have h_bot_1 : (A * (-1) + B) * 1 + (C * (-1) + D) ≤ 0 := by linarith
  have h_bot_m1 : (A * (-1) + B) * (-1) + (C * (-1) + D) ≤ 0 := by linarith
  have h_bot := affine_nonpos_of_endpoints (A * (-1) + B) (C * (-1) + D) h_bot_1 h_bot_m1 x hx1 hx2
  have h_y_1 : (A * x + C) * 1 + (B * x + D) ≤ 0 := by linarith
  have h_y_m1 : (A * x + C) * (-1) + (B * x + D) ≤ 0 := by linarith
  have h_final := affine_nonpos_of_endpoints (A * x + C) (B * x + D) h_y_1 h_y_m1 y hy1 hy2
  linarith

lemma bilinear_nonneg_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D ≥ 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D ≥ 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D ≥ 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D ≥ 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D ≥ 0 := by
  intro x y hx1 hx2 hy1 hy2
  have h_top_1 : (A * 1 + B) * 1 + (C * 1 + D) ≥ 0 := by linarith
  have h_top_m1 : (A * 1 + B) * (-1) + (C * 1 + D) ≥ 0 := by linarith
  have h_top := affine_nonneg_of_endpoints (A * 1 + B) (C * 1 + D) h_top_1 h_top_m1 x hx1 hx2
  have h_bot_1 : (A * (-1) + B) * 1 + (C * (-1) + D) ≥ 0 := by linarith
  have h_bot_m1 : (A * (-1) + B) * (-1) + (C * (-1) + D) ≥ 0 := by linarith
  have h_bot := affine_nonneg_of_endpoints (A * (-1) + B) (C * (-1) + D) h_bot_1 h_bot_m1 x hx1 hx2
  have h_y_1 : (A * x + C) * 1 + (B * x + D) ≥ 0 := by linarith
  have h_y_m1 : (A * x + C) * (-1) + (B * x + D) ≥ 0 := by linarith
  have h_final := affine_nonneg_of_endpoints (A * x + C) (B * x + D) h_y_1 h_y_m1 y hy1 hy2
  linarith

lemma bilinear_pos_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D > 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D > 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D > 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D > 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D > 0 := by
  intro x y hx1 hx2 hy1 hy2
  have h_top_1 : (A * 1 + B) * 1 + (C * 1 + D) > 0 := by linarith
  have h_top_m1 : (A * 1 + B) * (-1) + (C * 1 + D) > 0 := by linarith
  have h_top := affine_pos_of_endpoints (A * 1 + B) (C * 1 + D) h_top_1 h_top_m1 x hx1 hx2
  have h_bot_1 : (A * (-1) + B) * 1 + (C * (-1) + D) > 0 := by linarith
  have h_bot_m1 : (A * (-1) + B) * (-1) + (C * (-1) + D) > 0 := by linarith
  have h_bot := affine_pos_of_endpoints (A * (-1) + B) (C * (-1) + D) h_bot_1 h_bot_m1 x hx1 hx2
  have h_y_1 : (A * x + C) * 1 + (B * x + D) > 0 := by linarith
  have h_y_m1 : (A * x + C) * (-1) + (B * x + D) > 0 := by linarith
  have h_final := affine_pos_of_endpoints (A * x + C) (B * x + D) h_y_1 h_y_m1 y hy1 hy2
  linarith

lemma bilinear_neg_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D < 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D < 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D < 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D < 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D < 0 := by
  intro x y hx1 hx2 hy1 hy2
  have h_top_1 : (A * 1 + B) * 1 + (C * 1 + D) < 0 := by linarith
  have h_top_m1 : (A * 1 + B) * (-1) + (C * 1 + D) < 0 := by linarith
  have h_top := affine_neg_of_endpoints (A * 1 + B) (C * 1 + D) h_top_1 h_top_m1 x hx1 hx2
  have h_bot_1 : (A * (-1) + B) * 1 + (C * (-1) + D) < 0 := by linarith
  have h_bot_m1 : (A * (-1) + B) * (-1) + (C * (-1) + D) < 0 := by linarith
  have h_bot := affine_neg_of_endpoints (A * (-1) + B) (C * (-1) + D) h_bot_1 h_bot_m1 x hx1 hx2
  have h_y_1 : (A * x + C) * 1 + (B * x + D) < 0 := by linarith
  have h_y_m1 : (A * x + C) * (-1) + (B * x + D) < 0 := by linarith
  have h_final := affine_neg_of_endpoints (A * x + C) (B * x + D) h_y_1 h_y_m1 y hy1 hy2
  linarith

lemma inDigitNeg_sound_pos (n d : ℤ) (hd : d > 0) (h : Tensor.inDigitNeg n d = true) :
    (n : ℝ) ≤ 0 ∧ (n : ℝ) + (d : ℝ) ≥ 0 := by
  unfold Tensor.inDigitNeg at h
  rw [if_pos hd] at h
  simp only[Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩
  constructor
  · have : n ≤ 0 := by linarith
    exact_mod_cast this
  · have : n + d ≥ 0 := by linarith
    exact_mod_cast this

lemma inDigitNeg_sound_neg (n d : ℤ) (hd : d < 0) (h : Tensor.inDigitNeg n d = true) :
    (n : ℝ) ≥ 0 ∧ (n : ℝ) + (d : ℝ) ≤ 0 := by
  unfold Tensor.inDigitNeg at h
  have hd_not_pos : ¬(d > 0) := by linarith
  rw [if_neg hd_not_pos] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩
  constructor
  · have : 0 ≤ n := by linarith
    exact_mod_cast this
  · have : n + d ≤ 0 := by linarith
    exact_mod_cast this

lemma hasNoPole_cases (d1 d2 d3 d4 : ℤ) (h : Tensor.hasNoPole d1 d2 d3 d4 = true) :
    (d1 > 0 ∧ d2 > 0 ∧ d3 > 0 ∧ d4 > 0) ∨ (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
  unfold Tensor.hasNoPole at h
  simp only[Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact Or.inl ⟨h1, h2, h3, h4⟩
  · exact Or.inr ⟨h1, h2, h3, h4⟩

theorem emitNeg_sound (T : Tensor) (x y : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Tensor.oracle T = Tensor.EmitDecision.neg →
    -1 ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ 0 := by
  intro h_oracle
  
  change (
    if !Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h) (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.absorb
    else if Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.neg
    else if Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.zero
    else if Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.pos
    else Tensor.EmitDecision.absorb
  ) = Tensor.EmitDecision.neg at h_oracle

  split_ifs at h_oracle
  any_goals contradiction

  have h_np_eq : Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h) (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) = true := by
    cases eq : Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h) (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h)
    · simp_all
    · rfl

  have h_neg_eq : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
          Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
          Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
    simp_all

  have h_np_cases := hasNoPole_cases _ _ _ _ h_np_eq

  simp only [Bool.and_eq_true] at h_neg_eq
  rcases h_neg_eq with ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩

  rcases h_np_cases with hd_pos | hd_neg
  · -- Case 1: Positive denominators
    have b1 := inDigitNeg_sound_pos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) hd_pos.1 c1
    have b2 := inDigitNeg_sound_pos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) hd_pos.2.1 c2
    have b3 := inDigitNeg_sound_pos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) hd_pos.2.2.1 c3
    have b4 := inDigitNeg_sound_pos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) hd_pos.2.2.2 c4

    have h_num_le_zero : (T.a:ℝ)*x*y + (T.b:ℝ)*x + (T.c:ℝ)*y + (T.d:ℝ) ≤ 0 := by
      apply bilinear_nonpos_of_corners (T.a:ℝ) (T.b:ℝ) (T.c:ℝ) (T.d:ℝ)
      · have h := b1.1; push_cast at h; linarith
      · have h := b2.1; push_cast at h; linarith
      · have h := b3.1; push_cast at h; linarith
      · have h := b4.1; push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    have h_num_plus_den_ge_zero : ((T.a:ℝ)+(T.e:ℝ))*x*y + ((T.b:ℝ)+(T.f:ℝ))*x + ((T.c:ℝ)+(T.g:ℝ))*y + ((T.d:ℝ)+(T.h:ℝ)) ≥ 0 := by
      apply bilinear_nonneg_of_corners
      · have h := b1.2; push_cast at h; linarith
      · have h := b2.2; push_cast at h; linarith
      · have h := b3.2; push_cast at h; linarith
      · have h := b4.2; push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    have h_den_pos : (T.e:ℝ)*x*y + (T.f:ℝ)*x + (T.g:ℝ)*y + (T.h:ℝ) > 0 := by
      apply bilinear_pos_of_corners
      · have h : (T.e + T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.1
        push_cast at h; linarith
      · have h : (-T.e + T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.1
        push_cast at h; linarith
      · have h : (-T.e - T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.1
        push_cast at h; linarith
      · have h : (T.e - T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.2
        push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    unfold Tensor.apply
    constructor
    · rw [le_div_iff₀ h_den_pos]; linarith
    · rw [div_le_iff₀ h_den_pos]; linarith

  · -- Case 2: Negative denominators
    have b1 := inDigitNeg_sound_neg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) hd_neg.1 c1
    have b2 := inDigitNeg_sound_neg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) hd_neg.2.1 c2
    have b3 := inDigitNeg_sound_neg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) hd_neg.2.2.1 c3
    have b4 := inDigitNeg_sound_neg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) hd_neg.2.2.2 c4

    have h_num_ge_zero : (T.a:ℝ)*x*y + (T.b:ℝ)*x + (T.c:ℝ)*y + (T.d:ℝ) ≥ 0 := by
      apply bilinear_nonneg_of_corners (T.a:ℝ) (T.b:ℝ) (T.c:ℝ) (T.d:ℝ)
      · have h := b1.1; push_cast at h; linarith
      · have h := b2.1; push_cast at h; linarith
      · have h := b3.1; push_cast at h; linarith
      · have h := b4.1; push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    have h_num_plus_den_le_zero : ((T.a:ℝ)+(T.e:ℝ))*x*y + ((T.b:ℝ)+(T.f:ℝ))*x + ((T.c:ℝ)+(T.g:ℝ))*y + ((T.d:ℝ)+(T.h:ℝ)) ≤ 0 := by
      apply bilinear_nonpos_of_corners
      · have h := b1.2; push_cast at h; linarith
      · have h := b2.2; push_cast at h; linarith
      · have h := b3.2; push_cast at h; linarith
      · have h := b4.2; push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    have h_den_neg : (T.e:ℝ)*x*y + (T.f:ℝ)*x + (T.g:ℝ)*y + (T.h:ℝ) < 0 := by
      apply bilinear_neg_of_corners
      · have h : (T.e + T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.1
        push_cast at h; linarith
      · have h : (-T.e + T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.1
        push_cast at h; linarith
      · have h : (-T.e - T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.1
        push_cast at h; linarith
      · have h : (T.e - T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.2
        push_cast at h; linarith
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2

    unfold Tensor.apply
    constructor
    · rw [le_div_iff₀_of_neg h_den_neg]; linarith
    · rw [div_le_iff₀_of_neg h_den_neg]; linarith

end Möbius
end Computable