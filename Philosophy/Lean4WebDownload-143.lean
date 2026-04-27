import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Analytic Exact Real Arithmetic (Field-Complete PIVP)

A PIVP (Polynomial Initial Value Problem) representation of computable reals.
This module uses a "Two-World Architecture":
1. A Computable Execution Engine (using a custom Polynomial AST).
2. A Noncomputable Semantic Denotation mapping the execution to Classical `ℝ`.
-/

/-! =========================================================================
   PART 1: POLYNOMIAL AST
   ========================================================================== -/

/-- Computable AST for integer polynomials over variable type `V`.
    Renamed to `VPoly` to avoid clashing with Mathlib's `Poly`. -/
inductive VPoly (V : Type)
  | C : ℤ → VPoly V
  | X : V → VPoly V
  | add : VPoly V → VPoly V → VPoly V
  | mul : VPoly V → VPoly V → VPoly V
  | neg : VPoly V → VPoly V

namespace VPoly

variable {V : Type}

instance : Add (VPoly V) := ⟨VPoly.add⟩
instance : Mul (VPoly V) := ⟨VPoly.mul⟩
instance : Neg (VPoly V) := ⟨VPoly.neg⟩
instance : Sub (VPoly V) := ⟨fun p q => VPoly.add p (VPoly.neg q)⟩

/-- Evaluate in a `CommRing`. -/
def eval {R : Type}[CommRing R] (env : V → R) : VPoly V → R
  | C z => (z : R)
  | X v => env v
  | add p q => p.eval env + q.eval env
  | mul p q => p.eval env * q.eval env
  | neg p => -p.eval env

/-- Symbolic partial derivative. -/
def pderiv [DecidableEq V] (v : V) : VPoly V → VPoly V
  | C _ => C 0
  | X x => if x = v then C 1 else C 0
  | add p q => p.pderiv v + q.pderiv v
  | mul p q => p.pderiv v * q + p * q.pderiv v
  | neg p => VPoly.neg (p.pderiv v)

/-- Rename variables via `f : V → W`. -/
def rename {W : Type} (f : V → W) : VPoly V → VPoly W
  | C z => C z
  | X v => X (f v)
  | add p q => p.rename f + q.rename f
  | mul p q => p.rename f * q.rename f
  | neg p => VPoly.neg (p.rename f)

/-! ### `eval` simp lemmas -/
section EvalLemmas
variable {R : Type} [CommRing R]

@[simp] theorem eval_c (env : V → R) (z : ℤ) :
    (C z : VPoly V).eval env = (z : R) := rfl
@[simp] theorem eval_x (env : V → R) (v : V) :
    (X v : VPoly V).eval env = env v := rfl
@[simp] theorem eval_add' (env : V → R) (p q : VPoly V) :
    (VPoly.add p q).eval env = p.eval env + q.eval env := rfl
@[simp] theorem eval_mul' (env : V → R) (p q : VPoly V) :
    (VPoly.mul p q).eval env = p.eval env * q.eval env := rfl
@[simp] theorem eval_neg' (env : V → R) (p : VPoly V) :
    (VPoly.neg p).eval env = -p.eval env := rfl

@[simp] theorem eval_hadd (env : V → R) (p q : VPoly V) :
    (p + q).eval env = p.eval env + q.eval env := rfl
@[simp] theorem eval_hmul (env : V → R) (p q : VPoly V) :
    (p * q).eval env = p.eval env * q.eval env := rfl
@[simp] theorem eval_hneg (env : V → R) (p : VPoly V) :
    (-p).eval env = -p.eval env := rfl
end EvalLemmas

@[simp] theorem eval_rename {V W R : Type} [CommRing R]
    (f : V → W) (env : W → R) (p : VPoly V) :
    (p.rename f).eval env = p.eval (env ∘ f) := by
  induction p with
  | C _ => rfl
  | X _ => rfl
  | add _ _ ihp ihq => simp [rename, ihp, ihq]
  | mul _ _ ihp ihq => simp [rename, ihp, ihq]
  | neg _ ih => simp [rename, ih]

section PderivEval
variable [DecidableEq V] {R : Type} [CommRing R]

@[simp] theorem pderiv_c_eval (env : V → R) (v : V) (z : ℤ) :
    ((C z : VPoly V).pderiv v).eval env = 0 := by simp [pderiv]

theorem pderiv_x_eval (env : V → R) (v w : V) :
    ((X w : VPoly V).pderiv v).eval env = if w = v then 1 else 0 := by
  simp only [pderiv]; split_ifs <;> simp

@[simp] theorem pderiv_x_self_eval (env : V → R) (v : V) :
    ((X v : VPoly V).pderiv v).eval env = 1 := by
  simp [pderiv_x_eval]

theorem pderiv_x_ne_eval (env : V → R) {v w : V} (h : w ≠ v) :
    ((X w : VPoly V).pderiv v).eval env = 0 := by
  simp [pderiv_x_eval, h]
end PderivEval

/-! ### IsConst predicate -/

/-- A VPoly is "constant" if it contains no variables. -/
def IsConst : VPoly V → Prop
  | .C _ => True
  | .X _ => False
  | .add p q => p.IsConst ∧ q.IsConst
  | .mul p q => p.IsConst ∧ q.IsConst
  | .neg p => p.IsConst

lemma is_const_pderiv [DecidableEq V] (p : VPoly V) (v : V) :
    p.IsConst → (p.pderiv v).IsConst := by
  induction p with
  | C _ => intro _; exact trivial
  | X _ => intro h; exact False.elim h
  | add _ _ ih1 ih2 => intro h; exact ⟨ih1 h.1, ih2 h.2⟩
  | mul _ _ ih1 ih2 => intro h; exact ⟨⟨ih1 h.1, h.2⟩, ⟨h.1, ih2 h.2⟩⟩
  | neg _ ih => intro h; exact ih h

lemma eval_pderiv_of_is_const [DecidableEq V] {R : Type} [CommRing R]
    (p : VPoly V) (v : V) (env : V → R) :
    p.IsConst → (p.pderiv v).eval env = 0 := by
  induction p with
  | C _ => intro _; simp [pderiv]
  | X _ => intro h; exact False.elim h
  | add _ _ ih1 ih2 => intro h; simp [pderiv, ih1 h.1, ih2 h.2]
  | mul _ _ ih1 ih2 => intro h; simp [pderiv, ih1 h.1, ih2 h.2]
  | neg _ ih => intro h; simp [pderiv, ih h]

/-! ### MvPolynomial Bridge (for semantic derivative verification) -/
noncomputable def toMvPolynomial : VPoly V → MvPolynomial V ℚ
  | C z => MvPolynomial.C (z : ℚ)
  | X v => MvPolynomial.X v
  | add p q => p.toMvPolynomial + q.toMvPolynomial
  | mul p q => p.toMvPolynomial * q.toMvPolynomial
  | neg p => -p.toMvPolynomial

lemma toMvPolynomial_pderiv [DecidableEq V] (p : VPoly V) (v : V) :
    (p.pderiv v).toMvPolynomial = MvPolynomial.pderiv v p.toMvPolynomial := by
  induction p with
  | C z =>
    simp only [pderiv, toMvPolynomial]
    rw [MvPolynomial.pderiv_C]
    simp
  | X x =>
    simp only [pderiv]
    split_ifs with h
    · subst h; simp [toMvPolynomial, MvPolynomial.pderiv_X]
    · have hne : v ≠ x := fun heq => h heq.symm
      simp [toMvPolynomial, MvPolynomial.pderiv_X, hne]
  | add p q ihp ihq =>
    simp [pderiv, toMvPolynomial, ihp, ihq, map_add]
  | mul p q ihp ihq =>
    simp only [pderiv, toMvPolynomial]
    rw [MvPolynomial.pderiv_mul, ← ihp, ← ihq]
  | neg p ih =>
    simp [pderiv, toMvPolynomial, ih, map_neg]

lemma toMvPolynomial_rename {W : Type} (f : V → W) (p : VPoly V) :
    (p.rename f).toMvPolynomial = MvPolynomial.rename f p.toMvPolynomial := by
  induction p <;> simp [rename, toMvPolynomial, *]

lemma eval_eq_MvPolynomial_eval (P : VPoly V) (env : V → ℚ) :
    P.eval env = MvPolynomial.eval env P.toMvPolynomial := by
  induction P <;> simp [VPoly.eval, VPoly.toMvPolynomial, *]

end VPoly

/-! =========================================================================
   PART 2: PIVP STRUCTURE
   ========================================================================== -/

structure AnalyticReal (V : Type) [Fintype V] [DecidableEq V] where
  out : V
  init : V → ℚ
  deriv : V → VPoly V
  out_init_zero : init out = 0

namespace AnalyticReal

/-! =========================================================================
   PART 3: FIELD OPERATIONS
   ========================================================================== -/

def const (q : ℤ) : AnalyticReal Unit where
  out := ()
  init := fun _ => 0
  deriv := fun _ => VPoly.C q
  out_init_zero := rfl

def invM1 {V : Type} [Fintype V] [DecidableEq V]
    (ar : AnalyticReal V) : AnalyticReal (Option V) where
  out := none
  init v := match v with
    | none => 0
    | some x => ar.init x
  deriv v := match v with
    | none =>
        let dx := VPoly.rename some (ar.deriv ar.out)
        let z := VPoly.X (none : Option V)
        let z1 := z + VPoly.C 1
        VPoly.neg (z1 * z1 * dx)
    | some x => VPoly.rename some (ar.deriv x)
  out_init_zero := rfl

variable {V₁ V₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

def add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal (Option (V₁ ⊕ V₂)) where
  out := none
  init v := match v with
    | none => 0
    | some (Sum.inl x) => ar₁.init x
    | some (Sum.inr y) => ar₂.init y
  deriv v := match v with
    | none =>
        VPoly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out) +
        VPoly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
    | some (Sum.inl x) => VPoly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => VPoly.rename (some ∘ Sum.inr) (ar₂.deriv y)
  out_init_zero := rfl

def mul (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal (Option (V₁ ⊕ V₂)) where
  out := none
  init v := match v with
    | none => 0
    | some (Sum.inl x) => ar₁.init x
    | some (Sum.inr y) => ar₂.init y
  deriv v := match v with
    | none =>
        let dx := VPoly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out)
        let dy := VPoly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
        let xv := VPoly.X (some (Sum.inl ar₁.out))
        let yv := VPoly.X (some (Sum.inr ar₂.out))
        dx * yv + xv * dy
    | some (Sum.inl x) => VPoly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => VPoly.rename (some ∘ Sum.inr) (ar₂.deriv y)
  out_init_zero := rfl

/-! =========================================================================
   PART 4: PICARD CERTIFIER (Noncomputable)
   ========================================================================== -/

noncomputable def lieDeriv {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) : VPoly V :=
  (Finset.univ : Finset V).toList.foldl
    (fun acc v => acc + (F.pderiv v) * (dv v)) (VPoly.C 0)

noncomputable def lieIter {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : ℕ → VPoly V
  | 0 => VPoly.X A.out
  | i + 1 => lieDeriv A.deriv (lieIter A i)

noncomputable def taylorCoeff {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (k : ℕ) : ℚ :=
  (lieIter A k).eval A.init / (Nat.factorial k : ℚ)

open Finset

noncomputable def approxSum {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), taylorCoeff A k

/-! =========================================================================
   PART 5: SEMANTICS
   ========================================================================== -/

open Filter Topology

class IsAnalytic {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : Prop where
  convergence_proof : CauchySeq (fun n => (approxSum A n : ℝ))

noncomputable def toReal {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) [IsAnalytic A] : ℝ :=
  limUnder atTop (fun n => (approxSum A n : ℝ))

/-! =========================================================================
   PART 6: SEMANTIC BRIDGE AND BASE CASE
   ========================================================================== -/

/-- `(lieDeriv dv F).eval env = ∑ v, (∂F/∂v)(env) · dv(v)(env)`. -/
theorem lie_deriv_eval {V : Type} [Fintype V] [DecidableEq V]
    {R : Type} [CommRing R] (dv : V → VPoly V) (F : VPoly V) (env : V → R) :
    (lieDeriv dv F).eval env =
      ∑ v : V, (F.pderiv v).eval env * (dv v).eval env := by
  unfold lieDeriv
  set g : V → R := fun v => (F.pderiv v).eval env * (dv v).eval env
  suffices h : ∀ (acc : VPoly V) (l : List V),
      (l.foldl (fun a v => a + (F.pderiv v) * (dv v)) acc).eval env =
        acc.eval env + (l.map g).sum by
    have h₀ := h (VPoly.C 0) (Finset.univ : Finset V).toList
    simp only [VPoly.eval_c, Int.cast_zero, zero_add] at h₀
    rw [h₀, ← Finset.sum_toList]
  intro acc l
  induction l generalizing acc with
  | nil => simp [g]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, g]
    rw [ih]; simp; ring

/-! ### Evaluated Lie iterates for `const q` -/

theorem lie_iter_const_eval_zero (q : ℤ) :
    (lieIter (const q) 0).eval (const q).init = 0 := by
  simp [lieIter, const]

theorem lie_iter_const_eval_one (q : ℤ) :
    (lieIter (const q) 1).eval (const q).init = (q : ℚ) := by
  simp only [lieIter]
  have eq : (lieDeriv (const q).deriv (VPoly.X ())).eval (const q).init =
    ∑ v : Unit, ((VPoly.X ()).pderiv v).eval (const q).init *
      ((const q).deriv v).eval (const q).init :=
    lie_deriv_eval (V := Unit) (R := ℚ) _ _ _
  rw [eq]
  simp [const]

lemma foldl_is_const {V : Type} [DecidableEq V] (l : List V) (dv : V → VPoly V) (F : VPoly V)
    (acc : VPoly V)
    (hacc : acc.IsConst)
    (hdv : ∀ v ∈ l, (dv v).IsConst)
    (hF : ∀ v ∈ l, (F.pderiv v).IsConst) :
    (l.foldl (fun a v => a + F.pderiv v * dv v) acc).IsConst := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · refine ⟨hacc, hF hd ?_, hdv hd ?_⟩ <;> exact List.mem_cons_self hd tl
    · intro v hv; exact hdv v (List.mem_cons_of_mem _ hv)
    · intro v hv; exact hF v (List.mem_cons_of_mem _ hv)

lemma lie_deriv_is_const {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V)
    (hdv : ∀ v, (dv v).IsConst) (hF : ∀ v, (F.pderiv v).IsConst) :
    (lieDeriv dv F).IsConst := by
  apply foldl_is_const
  · exact trivial
  · intro v _; exact hdv v
  · intro v _; exact hF v

lemma lie_iter_const_is_const (q : ℤ) (k : ℕ) :
    (lieIter (const q) (k + 1)).IsConst := by
  induction k with
  | zero =>
    change (lieDeriv (fun _ => VPoly.C q) (VPoly.X ())).IsConst
    apply lie_deriv_is_const
    · intro v; exact trivial
    · intro v; cases v; simp [VPoly.pderiv, VPoly.IsConst]
  | succ k ih =>
    change (lieDeriv (fun _ => VPoly.C q) (lieIter (const q) (k + 1))).IsConst
    apply lie_deriv_is_const
    · intro _; exact trivial
    · intro v; exact VPoly.is_const_pderiv _ _ ih

theorem lie_iter_const_pderiv_eval_zero (q : ℤ) (k : ℕ) :
    ((lieIter (const q) (k + 1)).pderiv ()).eval (const q).init = 0 :=
  VPoly.eval_pderiv_of_is_const _ _ _ (lie_iter_const_is_const q k)

theorem lie_iter_const_eval_succ_succ (q : ℤ) (k : ℕ) :
    (lieIter (const q) (k + 2)).eval (const q).init = 0 := by
  change (lieDeriv (const q).deriv (lieIter (const q) (k + 1))).eval (const q).init = 0
  rw [lie_deriv_eval (V := Unit) (R := ℚ), Fintype.sum_unique,
      lie_iter_const_pderiv_eval_zero q k]
  ring

theorem taylor_coeff_const (q : ℤ) (k : ℕ) :
    taylorCoeff (const q) k =
      if k = 0 then 0 else if k = 1 then (q : ℚ) else 0 := by
  simp only [taylorCoeff]
  match k with
  | 0 => simp [lie_iter_const_eval_zero]
  | 1 => simp [lie_iter_const_eval_one, Nat.factorial]
  | n + 2 =>
    have h2 : n + 2 ≠ 1 := by omega
    simp [lie_iter_const_eval_succ_succ, h2]

theorem approx_sum_const (q : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    approxSum (const q) n = (q : ℚ) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn_zero : n = 0
    · subst hn_zero
      simp [approxSum, sum_range_succ, taylor_coeff_const]
    · have h_pos : 1 ≤ n := by omega
      have ih' := ih h_pos
      unfold approxSum
      rw [sum_range_succ]
      have h_coeff : taylorCoeff (const q) (n + 1) = 0 := by
        rw [taylor_coeff_const]
        have h1 : n + 1 ≠ 0 := by omega
        have h2 : n + 1 ≠ 1 := by omega
        simp [h1, h2]
      rw [h_coeff, add_zero]
      exact ih'

/-- The partial sums of `const q` converge to `q` in `ℝ`. -/
theorem const_tendsto (q : ℤ) :
    Tendsto (fun n => (approxSum (const q) n : ℝ)) atTop (nhds (q : ℝ)) := by
  rw [Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_atTop_sets]
  exact ⟨1, fun n hn => by
    have h := approx_sum_const q n hn
    have h2 : (approxSum (const q) n : ℝ) = (q : ℝ) := by
      rw [h]; push_cast; ring
    rw [Set.mem_preimage, h2]
    exact mem_of_mem_nhds hs⟩

noncomputable instance instIsAnalyticConst (q : ℤ) : IsAnalytic (const q) where
  convergence_proof := (const_tendsto q).cauchySeq

theorem to_real_const (q : ℤ) : toReal (const q) = (q : ℝ) :=
  (const_tendsto q).limUnder_eq

/-! =========================================================================
   PART 7: ADDITION SOUNDNESS
   ========================================================================== -/

section AddSoundness

variable {W₁ W₂ : Type}
  [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
  (ar₁ : AnalyticReal W₁) (ar₂ : AnalyticReal W₂)

theorem taylor_coeff_zero_eq {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : taylorCoeff A 0 = 0 := by
  simp [taylorCoeff, lieIter, A.out_init_zero]

/-! ### Sum lemmas for variable isolation tracking -/

lemma sum_option_eq {α M : Type} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (f : Option α → M) :
    ∑ x : Option α, f x = f none + ∑ x : α, f (some x) := by
  classical
  have : (Finset.univ : Finset (Option α)) =
      insert none (Finset.image some Finset.univ) := by
    ext x; cases x <;> simp
  rw [this, Finset.sum_insert]
  · rw [Finset.sum_image]
    · intro x _ y _ h; exact Option.some_inj.mp h
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x contra; cases contra

lemma sum_sum_eq {α β M : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] [AddCommMonoid M] (f : α ⊕ β → M) :
    ∑ x : α ⊕ β, f x = (∑ x : α, f (Sum.inl x)) + (∑ x : β, f (Sum.inr x)) := by
  classical
  have : (Finset.univ : Finset (α ⊕ β)) =
      (Finset.image Sum.inl Finset.univ) ∪ (Finset.image Sum.inr Finset.univ) := by
    ext x; cases x <;> simp
  rw [this, Finset.sum_union]
  · rw [Finset.sum_image, Finset.sum_image]
    · intro x _ y _ h; exact Sum.inr_injective h
    · intro x _ y _ h; exact Sum.inl_injective h
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    intro contra; cases contra

/-! ### Algebraic mapping for Lie iterates via MvPolynomial -/

lemma MvPolynomial_pderiv_X {V : Type} [DecidableEq V] (v w : V) :
    MvPolynomial.pderiv v (MvPolynomial.X w : MvPolynomial V ℚ) =
      if w = v then 1 else 0 := by
  rw [MvPolynomial.pderiv_X, Pi.single_apply]

lemma toMvPolynomial_lieDeriv {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) :
    (lieDeriv dv F).toMvPolynomial =
      ∑ v : V, MvPolynomial.pderiv v F.toMvPolynomial *
        (dv v).toMvPolynomial := by
  unfold lieDeriv
  set g : V → MvPolynomial V ℚ := fun v =>
    MvPolynomial.pderiv v F.toMvPolynomial * (dv v).toMvPolynomial
  suffices h : ∀ (acc : VPoly V) (l : List V),
      (l.foldl (fun a v => a + F.pderiv v * dv v) acc).toMvPolynomial =
        acc.toMvPolynomial + (l.map g).sum by
    have h₀ := h (VPoly.C 0) (Finset.univ : Finset V).toList
    simp only [VPoly.toMvPolynomial, Int.cast_zero, map_zero, zero_add] at h₀
    rw [h₀, ← Finset.sum_toList]
  intro acc l
  induction l generalizing acc with
  | nil => simp [g]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, g]
    rw [ih]
    simp [VPoly.toMvPolynomial, VPoly.toMvPolynomial_pderiv]
    ring

lemma toMvPolynomial_lieDeriv_add {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F G : VPoly V) :
    (lieDeriv dv (VPoly.add F G)).toMvPolynomial =
      (lieDeriv dv F).toMvPolynomial + (lieDeriv dv G).toMvPolynomial := by
  rw [toMvPolynomial_lieDeriv, toMvPolynomial_lieDeriv, toMvPolynomial_lieDeriv,
      VPoly.toMvPolynomial]
  simp [map_add, add_mul, Finset.sum_add_distrib]

lemma MvPolynomial_lieDeriv_congr {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F G : VPoly V)
    (h : F.toMvPolynomial = G.toMvPolynomial) :
    (lieDeriv dv F).toMvPolynomial = (lieDeriv dv G).toMvPolynomial := by
  rw [toMvPolynomial_lieDeriv, toMvPolynomial_lieDeriv]
  simp [h]

lemma toMvPolynomial_lieDeriv_X {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (v : V) :
    (lieDeriv dv (VPoly.X v)).toMvPolynomial = (dv v).toMvPolynomial := by
  rw [toMvPolynomial_lieDeriv]
  have h1 : ∑ x : V, MvPolynomial.pderiv x (VPoly.X v).toMvPolynomial *
      (dv x).toMvPolynomial = MvPolynomial.pderiv v (VPoly.X v).toMvPolynomial *
        (dv v).toMvPolynomial := by
    apply Finset.sum_eq_single v
    · intro b _ hb
      have hb_ne : v ≠ b := Ne.symm hb
      rw [VPoly.toMvPolynomial, MvPolynomial_pderiv_X]
      simp [hb_ne]
    · intro contra
      exact False.elim (contra (Finset.mem_univ v))
  rw [h1, VPoly.toMvPolynomial, MvPolynomial_pderiv_X]
  simp

lemma toMvPolynomial_pderiv_rename_ne {V W : Type} [DecidableEq V] [DecidableEq W]
    (f : V → W) (P : VPoly V) (w : W) (hw : ∀ v, f v ≠ w) :
    MvPolynomial.pderiv w (P.rename f).toMvPolynomial = 0 := by
  induction P with
  | C z =>
    simp only [VPoly.rename, VPoly.toMvPolynomial, MvPolynomial.pderiv_C]
  | X x =>
    simp only [VPoly.toMvPolynomial, VPoly.rename]
    rw [MvPolynomial_pderiv_X]
    have h : f x ≠ w := hw x
    simp [h]
  | add p q ihp ihq => simp [VPoly.toMvPolynomial, VPoly.rename, ihp, ihq]
  | mul p q ihp ihq => simp [VPoly.toMvPolynomial, VPoly.rename, ihp, ihq]
  | neg p ihp => simp [VPoly.toMvPolynomial, VPoly.rename, ihp]

lemma toMvPolynomial_pderiv_rename {V W : Type} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (P : VPoly V) (v : V) :
    MvPolynomial.pderiv (f v) (P.rename f).toMvPolynomial =
      ((P.pderiv v).rename f).toMvPolynomial := by
  induction P with
  | C z =>
    simp [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial, MvPolynomial.pderiv_C]
  | X x =>
    by_cases h : x = v
    · subst h
      simp [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial,
            MvPolynomial.pderiv_X, Pi.single_apply]
    · have hf_ne : f x ≠ f v := fun heq => h (hf heq)
      simp [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial,
            MvPolynomial.pderiv_X, Pi.single_apply, h, hf_ne]
  | add p q ihp ihq =>
    simp only [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial, map_add, ihp, ihq]
  | mul p q ihp ihq =>
    simp only [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial]
    rw [MvPolynomial.pderiv_mul, ← ihp, ← ihq]
    ring
  | neg p ihp =>
    simp only [VPoly.pderiv, VPoly.rename, VPoly.toMvPolynomial, map_neg, ihp]

lemma toMvPolynomial_rename_lieDeriv {V W : Type} [Fintype V] [DecidableEq V]
    [DecidableEq W]
    (f : V → W) (dv : V → VPoly V) (P : VPoly V) :
    ((lieDeriv dv P).rename f).toMvPolynomial =
      ∑ x : V, ((P.pderiv x).rename f).toMvPolynomial *
        ((dv x).rename f).toMvPolynomial := by
  unfold lieDeriv
  set g : V → MvPolynomial W ℚ := fun x =>
    ((P.pderiv x).rename f).toMvPolynomial * ((dv x).rename f).toMvPolynomial
  suffices h : ∀ (acc : VPoly V) (l : List V),
      ((l.foldl (fun a v => a + P.pderiv v * dv v) acc).rename f).toMvPolynomial =
        (acc.rename f).toMvPolynomial + (l.map g).sum by
    have h₀ := h (VPoly.C 0) (Finset.univ : Finset V).toList
    simp only [VPoly.rename, VPoly.toMvPolynomial, Int.cast_zero, map_zero,
        zero_add] at h₀
    rw [h₀, ← Finset.sum_toList]
  intro acc l
  induction l generalizing acc with
  | nil => simp [g]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, g]
    rw [ih]
    simp [VPoly.rename, VPoly.toMvPolynomial]
    ring

lemma toMvPolynomial_lieDeriv_rename_inl (P : VPoly W₁) :
    (lieDeriv (add ar₁ ar₂).deriv
      (P.rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl))).toMvPolynomial =
    ((lieDeriv ar₁.deriv P).rename
      (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial := by
  rw [toMvPolynomial_lieDeriv, toMvPolynomial_rename_lieDeriv]
  rw [sum_option_eq, sum_sum_eq]
  have h_none : MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from none)
      ((P.rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial) = 0 := by
    apply toMvPolynomial_pderiv_rename_ne; intro v contra; cases contra
  have h_inr : ∀ y, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inr y))
      ((P.rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial) = 0 := by
    intro y; apply toMvPolynomial_pderiv_rename_ne
    intro v contra; injection contra with h; cases h
  have h_inr_sum : (∑ x : W₂, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inr x))
      ((P.rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial) *
      ((add ar₁ ar₂).deriv (some (Sum.inr x))).toMvPolynomial) = 0 := by
    apply Finset.sum_eq_zero; intro x _; rw [h_inr x, zero_mul]
  have h_inl : ∀ x, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inl x))
      ((P.rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial) =
      ((P.pderiv x).rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial := by
    intro x; exact toMvPolynomial_pderiv_rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)
      (by intro a b h; injection h with h; injection h with h; exact h) P x
  have h_inl_deriv : ∀ x, ((add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomial =
      ((ar₁.deriv x).rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial := by
    intro x; rfl
  rw [h_none, zero_mul, zero_add, h_inr_sum, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [h_inl x, h_inl_deriv x]

lemma toMvPolynomial_lieDeriv_rename_inr (P : VPoly W₂) :
    (lieDeriv (add ar₁ ar₂).deriv
      (P.rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr))).toMvPolynomial =
    ((lieDeriv ar₂.deriv P).rename
      (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial := by
  rw [toMvPolynomial_lieDeriv, toMvPolynomial_rename_lieDeriv]
  rw [sum_option_eq, sum_sum_eq]
  have h_none : MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from none)
      ((P.rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial) = 0 := by
    apply toMvPolynomial_pderiv_rename_ne; intro v contra; cases contra
  have h_inl : ∀ x, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inl x))
      ((P.rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial) = 0 := by
    intro x; apply toMvPolynomial_pderiv_rename_ne
    intro v contra; injection contra with h; cases h
  have h_inl_sum : (∑ x : W₁, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inl x))
      ((P.rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial) *
      ((add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomial) = 0 := by
    apply Finset.sum_eq_zero; intro x _; rw [h_inl x, zero_mul]
  have h_inr : ∀ y, MvPolynomial.pderiv (show Option (W₁ ⊕ W₂) from some (Sum.inr y))
      ((P.rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial) =
      ((P.pderiv y).rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial := by
    intro y; exact toMvPolynomial_pderiv_rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)
      (by intro a b h; injection h with h; injection h with h; exact h) P y
  have h_inr_deriv : ∀ y, ((add ar₁ ar₂).deriv (some (Sum.inr y))).toMvPolynomial =
      ((ar₂.deriv y).rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial := by
    intro y; rfl
  rw [h_none, zero_mul, zero_add, h_inl_sum, zero_add]
  apply Finset.sum_congr rfl
  intro y _
  rw [h_inr y, h_inr_deriv y]

lemma toMvPolynomial_lieIter_add (k : ℕ) :
    (lieIter (add ar₁ ar₂) (k + 1)).toMvPolynomial =
    ((lieIter ar₁ (k + 1)).rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl)).toMvPolynomial +
    ((lieIter ar₂ (k + 1)).rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr)).toMvPolynomial := by
  induction k with
  | zero =>
    simp only [lieIter]
    rw [toMvPolynomial_lieDeriv_X]
    simp only [add, VPoly.toMvPolynomial]
    congr 1
    · rw [VPoly.toMvPolynomial_rename, toMvPolynomial_lieDeriv_X]
    · rw [VPoly.toMvPolynomial_rename, toMvPolynomial_lieDeriv_X]
  | succ k ih =>
    have h_step : lieIter (add ar₁ ar₂) (k + 2) =
        lieDeriv (add ar₁ ar₂).deriv (lieIter (add ar₁ ar₂) (k + 1)) := rfl
    rw [h_step]
    have h_eq : (lieIter (add ar₁ ar₂) (k + 1)).toMvPolynomial =
      (VPoly.add
        ((lieIter ar₁ (k + 1)).rename (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl))
        ((lieIter ar₂ (k + 1)).rename (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr))).toMvPolynomial := by
      rw [VPoly.toMvPolynomial]
      exact ih
    rw [MvPolynomial_lieDeriv_congr _ _ _ h_eq]
    rw [toMvPolynomial_lieDeriv_add]
    rw [toMvPolynomial_lieDeriv_rename_inl]
    rw [toMvPolynomial_lieDeriv_rename_inr]
    rfl

lemma taylorCoeff_add_succ (k : ℕ) :
    taylorCoeff (add ar₁ ar₂) (k + 1) =
      taylorCoeff ar₁ (k + 1) + taylorCoeff ar₂ (k + 1) := by
  unfold taylorCoeff
  rw [VPoly.eval_eq_MvPolynomial_eval]
  rw [toMvPolynomial_lieIter_add]
  simp only [map_add]
  rw [← VPoly.eval_eq_MvPolynomial_eval, ← VPoly.eval_eq_MvPolynomial_eval]
  rw [VPoly.eval_rename, VPoly.eval_rename]
  have h_init1 : (add ar₁ ar₂).init ∘ (show W₁ → Option (W₁ ⊕ W₂) from some ∘ Sum.inl) = ar₁.init := rfl
  have h_init2 : (add ar₁ ar₂).init ∘ (show W₂ → Option (W₁ ⊕ W₂) from some ∘ Sum.inr) = ar₂.init := rfl
  rw [h_init1, h_init2]
  ring

/-- Syntactic separation and sum linearity rigorously resolves the structural
    equivalence mapping identically without axioms. -/
theorem taylor_coeff_add (k : ℕ) :
    taylorCoeff (add ar₁ ar₂) k = taylorCoeff ar₁ k + taylorCoeff ar₂ k := by
  cases k with
  | zero => simp [taylor_coeff_zero_eq, add]
  | succ k => exact taylorCoeff_add_succ ar₁ ar₂ k

theorem approx_sum_add (n : ℕ) :
    approxSum (add ar₁ ar₂) n = approxSum ar₁ n + approxSum ar₂ n := by
  simp only [approxSum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  exact taylor_coeff_add ar₁ ar₂ x

noncomputable instance instIsAnalyticAdd [hX : IsAnalytic ar₁] [hY : IsAnalytic ar₂] :
    IsAnalytic (add ar₁ ar₂) where
  convergence_proof := by
    have h_eq : (fun n => (approxSum (add ar₁ ar₂) n : ℝ)) =
        (fun n => (approxSum ar₁ n : ℝ) + (approxSum ar₂ n : ℝ)) := by
      ext n; simp [approx_sum_add]
    rw [h_eq]
    exact hX.convergence_proof.add hY.convergence_proof

/-- **Semantic correctness of addition.** -/
theorem to_real_add [IsAnalytic ar₁] [IsAnalytic ar₂] :
    toReal (add ar₁ ar₂) = toReal ar₁ + toReal ar₂ := by
  simp only [toReal]
  have h_eq : (fun n => (approxSum (add ar₁ ar₂) n : ℝ)) =
      (fun n => (approxSum ar₁ n : ℝ) + (approxSum ar₂ n : ℝ)) := by
    ext n; simp [approx_sum_add]
  rw [h_eq]
  exact ((IsAnalytic.convergence_proof (A := ar₁)).tendsto_limUnder.add
    (IsAnalytic.convergence_proof (A := ar₂)).tendsto_limUnder).limUnder_eq

end AddSoundness

end AnalyticReal