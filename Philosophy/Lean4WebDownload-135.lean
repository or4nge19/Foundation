import Mathlib

/-!
# Analytic Exact Real Arithmetic (Field-Complete PIVP)

A PIVP (Polynomial Initial Value Problem) representation of computable reals.

## Proof Obligation Summary

Four `sorry` obligations remain, each with correct type and clear documentation:
1. `toList_map_sum_eq_finset_sum` — connects `Finset.toList` to `Finset.sum`
2. `lieIter_const_pderiv_eval_zero` — pderiv of Lie iterates vanishes at init
3. `approxSum_const` — partial sums eventually equal `q`
4. `taylorCoeff_add` for `k ≥ 1` — Lie iterate decomposition for addition

All other proofs are complete. The dependency graph is:
  (1) → lieDeriv_eval → lieIter_const_eval_one / lieIter_const_eval_succ_succ
  (2) → lieIter_const_eval_succ_succ → taylorCoeff_const
  (3) → const_tendsto → const_isAnalytic / toReal_const
  (4) → taylorCoeff_add → approxSum_add → add_isAnalytic / toReal_add
-/

namespace Computable.Analytic

/-! =========================================================================
   PART 1: POLYNOMIAL AST
   ========================================================================== -/

/-- Computable AST for integer polynomials over variable type `V`. -/
inductive Poly (V : Type)
  | C : ℤ → Poly V
  | X : V → Poly V
  | add : Poly V → Poly V → Poly V
  | mul : Poly V → Poly V → Poly V
  | neg : Poly V → Poly V

namespace Poly

variable {V : Type}

instance : Add (Poly V) := ⟨Poly.add⟩
instance : Mul (Poly V) := ⟨Poly.mul⟩
instance : Neg (Poly V) := ⟨Poly.neg⟩
instance : Sub (Poly V) := ⟨fun p q => Poly.add p (Poly.neg q)⟩

/-- Evaluate in a `CommRing`. -/
def eval {R : Type} [CommRing R] (env : V → R) : Poly V → R
  | C z => (z : R)
  | X v => env v
  | add p q => p.eval env + q.eval env
  | mul p q => p.eval env * q.eval env
  | neg p => -(p.eval env)

/-- Symbolic partial derivative. -/
def pderiv [DecidableEq V] (v : V) : Poly V → Poly V
  | C _ => C 0
  | X x => if x = v then C 1 else C 0
  | add p q => p.pderiv v + q.pderiv v
  | mul p q => p.pderiv v * q + p * q.pderiv v
  | neg p => Poly.neg (p.pderiv v)

/-- Rename variables via `f : V → W`. -/
def rename {W : Type} (f : V → W) : Poly V → Poly W
  | C z => C z
  | X v => X (f v)
  | add p q => p.rename f + q.rename f
  | mul p q => p.rename f * q.rename f
  | neg p => Poly.neg (p.rename f)

/-! ### `eval` simp lemmas -/
section EvalLemmas
variable {R : Type} [CommRing R]

@[simp] theorem eval_C (env : V → R) (z : ℤ) :
    (C z : Poly V).eval env = (z : R) := rfl
@[simp] theorem eval_X (env : V → R) (v : V) :
    (X v : Poly V).eval env = env v := rfl
@[simp] theorem eval_add' (env : V → R) (p q : Poly V) :
    (Poly.add p q).eval env = p.eval env + q.eval env := rfl
@[simp] theorem eval_mul' (env : V → R) (p q : Poly V) :
    (Poly.mul p q).eval env = p.eval env * q.eval env := rfl
@[simp] theorem eval_neg' (env : V → R) (p : Poly V) :
    (Poly.neg p).eval env = -(p.eval env) := rfl
@[simp] theorem eval_hadd (env : V → R) (p q : Poly V) :
    (p + q).eval env = p.eval env + q.eval env := rfl
@[simp] theorem eval_hmul (env : V → R) (p q : Poly V) :
    (p * q).eval env = p.eval env * q.eval env := rfl
@[simp] theorem eval_hneg (env : V → R) (p : Poly V) :
    (-p).eval env = -(p.eval env) := rfl
end EvalLemmas

@[simp] theorem eval_rename {V W R : Type} [CommRing R]
    (f : V → W) (env : W → R) (p : Poly V) :
    (p.rename f).eval env = p.eval (env ∘ f) := by
  induction p with
  | C _ => rfl
  | X _ => rfl
  | add _ _ ihp ihq => simp [rename, ihp, ihq]
  | mul _ _ ihp ihq => simp [rename, ihp, ihq]
  | neg _ ih => simp [rename, ih]

section PderivEval
variable [DecidableEq V] {R : Type} [CommRing R]

@[simp] theorem pderiv_C_eval (env : V → R) (v : V) (z : ℤ) :
    ((C z : Poly V).pderiv v).eval env = 0 := by simp [pderiv]

theorem pderiv_X_eval (env : V → R) (v w : V) :
    ((X w : Poly V).pderiv v).eval env = if w = v then 1 else 0 := by
  simp only [pderiv]; split_ifs <;> simp

@[simp] theorem pderiv_X_self_eval (env : V → R) (v : V) :
    ((X v : Poly V).pderiv v).eval env = 1 := by
  simp [pderiv_X_eval]

theorem pderiv_X_ne_eval (env : V → R) {v w : V} (h : w ≠ v) :
    ((X w : Poly V).pderiv v).eval env = 0 := by
  simp [pderiv_X_eval, h]
end PderivEval

end Poly

/-! =========================================================================
   PART 2: PIVP STRUCTURE
   ========================================================================== -/

structure AnalyticReal (V : Type) [Fintype V] [DecidableEq V] where
  out : V
  init : V → ℚ
  deriv : V → Poly V
  out_init_zero : init out = 0

/-! =========================================================================
   PART 3: FIELD OPERATIONS
   ========================================================================== -/

def const (q : ℤ) : AnalyticReal Unit where
  out := ()
  init := fun _ => 0
  deriv := fun _ => Poly.C q
  out_init_zero := rfl

def invM1 {V : Type} [Fintype V] [DecidableEq V]
    (ar : AnalyticReal V) : AnalyticReal (Option V) where
  out := none
  init v := match v with
    | none => 0
    | some x => ar.init x
  deriv v := match v with
    | none =>
        let dx := Poly.rename some (ar.deriv ar.out)
        let z := Poly.X (none : Option V)
        let z1 := z + Poly.C 1
        Poly.neg (z1 * z1 * dx)
    | some x => Poly.rename some (ar.deriv x)
  out_init_zero := rfl

variable {V₁ V₂ : Type}
  [Fintype V₁] [DecidableEq V₁]
  [Fintype V₂] [DecidableEq V₂]

def add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal (Option (V₁ ⊕ V₂)) where
  out := none
  init v := match v with
    | none => 0
    | some (Sum.inl x) => ar₁.init x
    | some (Sum.inr y) => ar₂.init y
  deriv v := match v with
    | none =>
        Poly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out) +
        Poly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
    | some (Sum.inl x) => Poly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => Poly.rename (some ∘ Sum.inr) (ar₂.deriv y)
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
        let dx := Poly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out)
        let dy := Poly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
        let xv := Poly.X (some (Sum.inl ar₁.out))
        let yv := Poly.X (some (Sum.inr ar₂.out))
        dx * yv + xv * dy
    | some (Sum.inl x) => Poly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => Poly.rename (some ∘ Sum.inr) (ar₂.deriv y)
  out_init_zero := rfl

/-! =========================================================================
   PART 4: PICARD CERTIFIER (Noncomputable)
   ========================================================================== -/

noncomputable def lieDeriv {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → Poly V) (F : Poly V) : Poly V :=
  (Finset.univ : Finset V).toList.foldl
    (fun acc v => acc + (F.pderiv v) * (dv v)) (Poly.C 0)

noncomputable def lieIter {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : ℕ → Poly V
  | 0 => Poly.X A.out
  | i + 1 => lieDeriv A.deriv (lieIter A i)

noncomputable def taylorCoeff {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (k : ℕ) : ℚ :=
  (lieIter A k).eval A.init / (Nat.factorial k : ℚ)

noncomputable def approxSum {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun acc k => acc + taylorCoeff A k) 0

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

/-! ### Auxiliary lemmas -/

/-- `List.foldl (· + f ·) 0 l = (l.map f).sum` for `AddCommMonoid`. -/
theorem foldl_add_eq_sum_map {α R : Type} [AddCommMonoid R]
    (f : α → R) (l : List α) :
    l.foldl (fun acc a => acc + f a) 0 = (l.map f).sum := by
  suffices gen : ∀ (r : R) (l : List α),
      l.foldl (fun acc a => acc + f a) r = r + (l.map f).sum by
    simpa using gen 0 l
  intro r l'
  induction l' generalizing r with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]; abel

/--
**SORRY OBLIGATION 1**: `(s.toList.map f).sum = s.sum f` for a `Finset`.

This is a standard fact: `Finset.sum` is defined via `Multiset.sum`,
and `s.toList` enumerates the same elements as `s.val` (up to permutation),
so sums over `AddCommMonoid` agree.
-/
theorem toList_map_sum_eq_finset_sum {α M : Type} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (s.toList.map f).sum = s.sum f := by
  sorry

/-! ### The core bridge -/

/-- `(lieDeriv dv F).eval env = ∑ v, (∂F/∂v)(env) · dv(v)(env)`. -/
theorem lieDeriv_eval {V : Type} [Fintype V] [DecidableEq V]
    {R : Type} [CommRing R] (dv : V → Poly V) (F : Poly V) (env : V → R) :
    (lieDeriv dv F).eval env =
      ∑ v : V, (F.pderiv v).eval env * (dv v).eval env := by
  unfold lieDeriv
  set g : V → R := fun v => (F.pderiv v).eval env * (dv v).eval env
  -- Step 1: Commute `eval env` through the `Poly`-level foldl.
  suffices h : ∀ (acc : Poly V) (l : List V),
      (l.foldl (fun a v => a + (F.pderiv v) * (dv v)) acc).eval env =
        acc.eval env + (l.map g).sum by
    have h₀ := h (Poly.C 0) (Finset.univ : Finset V).toList
    simp only [Poly.eval_C, Int.cast_zero, zero_add] at h₀
    rw [h₀]
    -- Step 2: Relate list sum to Finset.sum.
    exact (toList_map_sum_eq_finset_sum Finset.univ g).symm
  -- Prove Step 1 by induction on the list.
  intro acc l
  induction l generalizing acc with
  | nil => simp [g]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, g]
    rw [ih]
    simp; ring

/-- `approxSum` as a list sum of `taylorCoeff`. -/
theorem approxSum_as_sum {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) :
    approxSum A n = ((List.range (n + 1)).map (taylorCoeff A)).sum :=
  foldl_add_eq_sum_map (taylorCoeff A) (List.range (n + 1))

/-! ### Evaluated Lie iterates for `const q` -/

theorem lieIter_const_eval_zero (q : ℤ) :
    (lieIter (const q) 0).eval (const q).init = 0 := by
  simp [lieIter, const]

theorem lieIter_const_eval_one (q : ℤ) :
    (lieIter (const q) 1).eval (const q).init = (q : ℚ) := by
  simp only [lieIter]
  rw [lieDeriv_eval]
  rw [Fintype.sum_unique]  -- ∑ v : Unit, f v = f ()
  simp [const]

/--
**SORRY OBLIGATION 2**: For `k ≥ 1`, `(∂(lieIter (const q) k)/∂()).eval init = 0`.

Proof strategy: by induction on `k`.
- Base (`k = 0`): `lieIter 1` is the Poly-level expression
  `C 0 + C 1 * C q`, built by `lieDeriv`. Its `pderiv ()` is
  `C 0 + (C 0 * C q + C 1 * C 0)`, which evaluates to `0 + (0·q + 1·0) = 0`.
  The difficulty is that `lieDeriv` produces this via `List.foldl`, so
  the syntactic form depends on `Finset.univ.toList` for `Unit`.
- Step (`k → k+1`): `lieIter (k+2) = lieDeriv (fun _ => C q) (lieIter (k+1))`.
  Its `pderiv ()` involves `∂²(lieIter (k+1))/∂()²`, which evaluates to 0
  by a strengthened inductive hypothesis.
-/
theorem lieIter_const_pderiv_eval_zero (q : ℤ) :
    ∀ k : ℕ, ((lieIter (const q) (k + 1)).pderiv ()).eval (const q).init = 0 := by
  sorry

theorem lieIter_const_eval_succ_succ (q : ℤ) (k : ℕ) :
    (lieIter (const q) (k + 2)).eval (const q).init = 0 := by
  simp only [lieIter]
  rw [lieDeriv_eval]
  rw [Fintype.sum_unique]
  simp only [const, Poly.eval_C]
  rw [lieIter_const_pderiv_eval_zero q k]
  ring

theorem taylorCoeff_const (q : ℤ) (k : ℕ) :
    taylorCoeff (const q) k =
      if k = 0 then 0 else if k = 1 then (q : ℚ) else 0 := by
  simp only [taylorCoeff]
  match k with
  | 0 => simp [lieIter_const_eval_zero]
  | 1 => simp [lieIter_const_eval_one, Nat.factorial]
  | n + 2 => simp [lieIter_const_eval_succ_succ]

/--
**SORRY OBLIGATION 3**: For `n ≥ 1`, `approxSum (const q) n = q`.

The list sum `∑_{k=0}^{n} taylorCoeff (const q) k = 0 + q + 0 + ⋯ + 0 = q`.
This follows from `taylorCoeff_const` and the fact that a list sum with
exactly one nonzero term at index 1 equals that term.
-/
theorem approxSum_const (q : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    approxSum (const q) n = (q : ℚ) := by
  sorry

/-- The partial sums of `const q` converge to `q` in `ℝ`. -/
theorem const_tendsto (q : ℤ) :
    Tendsto (fun n => (approxSum (const q) n : ℝ)) atTop (nhds (q : ℝ)) := by
  rw [Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_atTop_sets]
  exact ⟨1, fun n hn => by
    have h := approxSum_const q n hn
    have : (approxSum (const q) n : ℝ) = (q : ℝ) := by
      rw [h]; push_cast; ring
    rw [this]
    exact mem_of_mem_nhds hs⟩

noncomputable instance const_isAnalytic (q : ℤ) : IsAnalytic (const q) where
  convergence_proof := (const_tendsto q).cauchySeq

theorem toReal_const (q : ℤ) : toReal (const q) = (q : ℝ) :=
  (const_tendsto q).limUnder_eq

/-! =========================================================================
   PART 7: ADDITION SOUNDNESS
   ========================================================================== -/

section AddSoundness

variable {W₁ W₂ : Type}
  [Fintype W₁] [DecidableEq W₁]
  [Fintype W₂] [DecidableEq W₂]
  (ar₁ : AnalyticReal W₁) (ar₂ : AnalyticReal W₂)

/-! ### Variable isolation -/

theorem pderiv_rename_inl_wrt_inr_eval
    {A B : Type} [DecidableEq A] [DecidableEq B]
    {R : Type} [CommRing R] (env : (A ⊕ B) → R) (p : Poly A) (b : B) :
    ((p.rename Sum.inl).pderiv (Sum.inr b)).eval env = 0 := by
  induction p with
  | C _ => simp [Poly.rename, Poly.pderiv]
  | X a =>
    simp only [Poly.rename, Poly.pderiv]
    have : Sum.inl a ≠ Sum.inr b := Sum.inl_ne_inr
    simp [this]
  | add _ _ ih₁ ih₂ => simp [Poly.rename, Poly.pderiv, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [Poly.rename, Poly.pderiv, ih₁, ih₂]
  | neg _ ih => simp [Poly.rename, Poly.pderiv, ih]

theorem pderiv_rename_inr_wrt_inl_eval
    {A B : Type} [DecidableEq A] [DecidableEq B]
    {R : Type} [CommRing R] (env : (A ⊕ B) → R) (p : Poly B) (a : A) :
    ((p.rename Sum.inr).pderiv (Sum.inl a)).eval env = 0 := by
  induction p with
  | C _ => simp [Poly.rename, Poly.pderiv]
  | X b =>
    simp only [Poly.rename, Poly.pderiv]
    have : Sum.inr b ≠ Sum.inl a := Sum.inr_ne_inl
    simp [this]
  | add _ _ ih₁ ih₂ => simp [Poly.rename, Poly.pderiv, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [Poly.rename, Poly.pderiv, ih₁, ih₂]
  | neg _ ih => simp [Poly.rename, Poly.pderiv, ih]

/-! ### Taylor coefficient decomposition -/

theorem taylorCoeff_zero_eq {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : taylorCoeff A 0 = 0 := by
  simp [taylorCoeff, lieIter, A.out_init_zero]

/--
**SORRY OBLIGATION 4**: Taylor coefficients of `add ar₁ ar₂` decompose
as the sum of individual coefficients, for `k ≥ 1`.

Proof strategy: by induction on `k`, using `lieDeriv_eval` at each step.
The Lie derivative of the combined output decomposes because:
- The output derivative is `deriv₁(out₁) + deriv₂(out₂)` (sum of renamed polys).
- Variable isolation kills cross terms: `(∂(rename inl p)/∂(inr v)).eval = 0`.
- The combined `init` restricts to individual `init` on each subsystem.
-/
theorem taylorCoeff_add (k : ℕ) :
    taylorCoeff (add ar₁ ar₂) k = taylorCoeff ar₁ k + taylorCoeff ar₂ k := by
  rcases k with _ | k'
  · -- k = 0: all three are 0.
    simp [taylorCoeff_zero_eq]
  · -- k ≥ 1: Lie iterate decomposition.
    sorry

/-- List-level decomposition: `∑ (fᵢ + gᵢ) = ∑ fᵢ + ∑ gᵢ`. -/
private theorem list_sum_map_add {α M : Type} [AddCommMonoid M]
    (f g : α → M) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; abel

theorem approxSum_add (n : ℕ) :
    approxSum (add ar₁ ar₂) n = approxSum ar₁ n + approxSum ar₂ n := by
  simp only [approxSum_as_sum]
  have h_map : (List.range (n + 1)).map (taylorCoeff (add ar₁ ar₂)) =
      (List.range (n + 1)).map (fun k => taylorCoeff ar₁ k + taylorCoeff ar₂ k) := by
    congr 1; ext k; exact taylorCoeff_add ar₁ ar₂ k
  rw [h_map]
  exact list_sum_map_add (taylorCoeff ar₁) (taylorCoeff ar₂) (List.range (n + 1))

noncomputable instance add_isAnalytic
    [hX : IsAnalytic ar₁] [hY : IsAnalytic ar₂] :
    IsAnalytic (add ar₁ ar₂) where
  convergence_proof := by
    have h_eq : (fun n => (approxSum (add ar₁ ar₂) n : ℝ)) =
        (fun n => (approxSum ar₁ n : ℝ) + (approxSum ar₂ n : ℝ)) := by
      ext n; simp [approxSum_add]; push_cast; ring
    rw [h_eq]
    exact hX.convergence_proof.add hY.convergence_proof

/-- **Semantic correctness of addition.** -/
theorem toReal_add [IsAnalytic ar₁] [IsAnalytic ar₂] :
    toReal (add ar₁ ar₂) = toReal ar₁ + toReal ar₂ := by
  simp only [toReal]
  have h_eq : (fun n => (approxSum (add ar₁ ar₂) n : ℝ)) =
      (fun n => (approxSum ar₁ n : ℝ) + (approxSum ar₂ n : ℝ)) := by
    ext n; simp [approxSum_add]; push_cast; ring
  rw [h_eq]
  exact ((IsAnalytic.convergence_proof (A := ar₁)).tendsto_limUnder.add
    (IsAnalytic.convergence_proof (A := ar₂)).tendsto_limUnder).limUnder_eq

end AddSoundness

end Computable.Analytic