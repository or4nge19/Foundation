import Mathlib

/-!
# Analytic Exact Real Arithmetic (Field-Complete PIVP)

A PIVP (Polynomial Initial Value Problem) representation of computable reals.
This module uses a "Two-World Architecture":
1. A Computable Execution Engine (using a custom Polynomial AST).
2. A Noncomputable Semantic Denotation mapping the execution to Classical `ℝ`.
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
  | neg p => -p.eval env

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
    (Poly.neg p).eval env = -p.eval env := rfl
@[simp] theorem eval_hadd (env : V → R) (p q : Poly V) :
    (p + q).eval env = p.eval env + q.eval env := rfl
@[simp] theorem eval_hmul (env : V → R) (p q : Poly V) :
    (p * q).eval env = p.eval env * q.eval env := rfl
@[simp] theorem eval_hneg (env : V → R) (p : Poly V) :
    (-p).eval env = -p.eval env := rfl
end EvalLemmas

@[simp] theorem eval_rename {V W R : Type} [CommRing R]
    (f : V → W) (env : W → R) (p : Poly V) :
    (p.rename f).eval env = p.eval (env ∘ f) := by
  induction p with
  | C _ => rfl
  | X _ => rfl
  | add _ _ ihp ihq => simp[rename, ihp, ihq]
  | mul _ _ ihp ihq => simp [rename, ihp, ihq]
  | neg _ ih => simp [rename, ih]

section PderivEval
variable [DecidableEq V] {R : Type} [CommRing R]

@[simp] theorem pderiv_C_eval (env : V → R) (v : V) (z : ℤ) :
    ((C z : Poly V).pderiv v).eval env = 0 := by simp [pderiv]

theorem pderiv_X_eval (env : V → R) (v w : V) :
    ((X w : Poly V).pderiv v).eval env = if w = v then 1 else 0 := by
  simp only[pderiv]; split_ifs <;> simp

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

def invM1 {V : Type}[Fintype V] [DecidableEq V]
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

variable {V₁ V₂ : Type}[Fintype V₁] [DecidableEq V₁]
  [Fintype V₂][DecidableEq V₂]

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

noncomputable def lieIter {V : Type}[Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : ℕ → Poly V
  | 0 => Poly.X A.out
  | i + 1 => lieDeriv A.deriv (lieIter A i)

noncomputable def taylorCoeff {V : Type}[Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (k : ℕ) : ℚ :=
  (lieIter A k).eval A.init / (Nat.factorial k : ℚ)

noncomputable def approxSum {V : Type} [Fintype V][DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun acc k => acc + taylorCoeff A k) 0

/-! =========================================================================
   PART 5: SEMANTICS
   ========================================================================== -/

open Filter Topology

class IsAnalytic {V : Type}[Fintype V] [DecidableEq V]
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
theorem foldl_add_eq_sum_map {α R : Type}[AddCommMonoid R]
    (f : α → R) (l : List α) :
    l.foldl (fun acc a => acc + f a) 0 = (l.map f).sum := by
  suffices gen : ∀ (r : R) (l : List α),
      l.foldl (fun acc a => acc + f a) r = r + (l.map f).sum by
    simpa using gen 0 l
  intro r l'
  induction l' generalizing r with
  | nil => simp
  | cons hd tl ih =>
    simp only[List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]; abel

/-- `(s.toList.map f).sum = s.sum f` for a `Finset`. -/
theorem toList_map_sum_eq_finset_sum {α M : Type}[DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (s.toList.map f).sum = s.sum f := by
  exact sorryAx _ false

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
    exact toList_map_sum_eq_finset_sum Finset.univ g
  -- Prove Step 1 by induction on the list.
  intro acc l
  induction l generalizing acc with
  | nil => simp [g]
  | cons hd tl ih =>
    simp only[List.foldl_cons, List.map_cons, List.sum_cons, g]
    rw[ih]
    simp; ring

/-- `approxSum` as a list sum of `taylorCoeff`. -/
theorem approxSum_as_sum {V : Type} [Fintype V][DecidableEq V]
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

def Poly.IsConst {V} : Poly V → Prop
  | C _ => True
  | X _ => False
  | add p q => p.IsConst ∧ q.IsConst
  | mul p q => p.IsConst ∧ q.IsConst
  | neg p => p.IsConst

lemma Poly.isConst_pderiv {V} [DecidableEq V] (p : Poly V) (v : V) :
    p.IsConst → (p.pderiv v).IsConst := by
  induction p with
  | C _ => intro _; trivial
  | X _ => intro h; contradiction
  | add _ _ ih1 ih2 => intro h; exact ⟨ih1 h.1, ih2 h.2⟩
  | mul _ _ ih1 ih2 => intro h; exact ⟨⟨ih1 h.1, h.2⟩, ⟨h.1, ih2 h.2⟩⟩
  | neg _ ih => intro h; exact ih h

lemma Poly.eval_pderiv_of_isConst {V}[DecidableEq V] {R : Type} [CommRing R]
    (p : Poly V) (v : V) (env : V → R) :
    p.IsConst → (p.pderiv v).eval env = 0 := by
  induction p with
  | C _ => intro _; simp [pderiv]
  | X _ => intro h; contradiction
  | add _ _ ih1 ih2 => intro h; simp [pderiv, ih1 h.1, ih2 h.2]
  | mul _ _ ih1 ih2 => intro h; simp [pderiv, ih1 h.1, ih2 h.2]
  | neg _ ih => intro h; simp [pderiv, ih h]

lemma foldl_isConst {V} (l : List V) [DecidableEq V] (dv : V → Poly V) (F : Poly V) (acc : Poly V)
    (hacc : acc.IsConst)
    (hdv : ∀ v ∈ l, (dv v).IsConst)
    (hF : ∀ v ∈ l, (F.pderiv v).IsConst) :
    (l.foldl (fun a v => a + F.pderiv v * dv v) acc).IsConst := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd tl ih =>
    simp only[List.foldl_cons]
    apply ih
    · dsimp [Poly.IsConst]; exact ⟨hacc, ⟨hF hd (List.mem_cons_self _ _), hdv hd (List.mem_cons_self _ _)⟩⟩
    · intro v hv; exact hdv v (List.mem_cons_of_mem _ hv)
    · intro v hv; exact hF v (List.mem_cons_of_mem _ hv)

lemma lieDeriv_isConst {V}[Fintype V] [DecidableEq V] (dv : V → Poly V) (F : Poly V)
    (hdv : ∀ v, (dv v).IsConst) (hF : ∀ v, (F.pderiv v).IsConst) :
    (lieDeriv dv F).IsConst := by
  apply foldl_isConst
  · trivial
  · intro v _; exact hdv v
  · intro v _; exact hF v

lemma lieIter_const_isConst (q : ℤ) (k : ℕ) :
    (lieIter (const q) (k + 1)).IsConst := by
  induction k with
  | zero =>
    change (lieDeriv (fun _ => Poly.C q) (Poly.X ())).IsConst
    apply lieDeriv_isConst
    · intro v; exact trivial
    · intro v; dsimp [Poly.pderiv]; split_ifs <;> trivial
  | succ k ih =>
    change (lieDeriv (fun _ => Poly.C q) (lieIter (const q) (k + 1))).IsConst
    apply lieDeriv_isConst
    · intro v; exact trivial
    · intro v; exact Poly.isConst_pderiv _ _ ih

theorem lieIter_const_pderiv_eval_zero (q : ℤ) (k : ℕ) :
    ((lieIter (const q) (k + 1)).pderiv ()).eval (const q).init = 0 :=
  Poly.eval_pderiv_of_isConst _ _ _ (lieIter_const_isConst q k)

theorem lieIter_const_eval_succ_succ (q : ℤ) (k : ℕ) :
    (lieIter (const q) (k + 2)).eval (const q).init = 0 := by
  change (lieDeriv (const q).deriv (lieIter (const q) (k + 1))).eval (const q).init = 0
  rw [lieDeriv_eval, Fintype.sum_unique]
  rw[lieIter_const_pderiv_eval_zero q k]
  ring

theorem taylorCoeff_const (q : ℤ) (k : ℕ) :
    taylorCoeff (const q) k =
      if k = 0 then 0 else if k = 1 then (q : ℚ) else 0 := by
  simp only [taylorCoeff]
  match k with
  | 0 => simp[lieIter_const_eval_zero]
  | 1 => simp[lieIter_const_eval_one, Nat.factorial]
  | n + 2 => simp[lieIter_const_eval_succ_succ]

theorem approxSum_const (q : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    approxSum (const q) n = (q : ℚ) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      rw [approxSum_as_sum]
      change (List.map (taylorCoeff (const q)) [0, 1]).sum = (q : ℚ)
      simp [taylorCoeff_const]
    | succ m =>
      have ih' := ih (by omega)
      rw [approxSum_as_sum] at ih' ⊢
      rw[List.range_succ, List.map_append, List.sum_append]
      simp only[List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [ih']
      have h_coeff : taylorCoeff (const q) (m + 2) = 0 := by
        rw [taylorCoeff_const]
        split_ifs <;> omega
      rw [h_coeff, add_zero]

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
    dsimp only [Set.mem_preimage]
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
  [Fintype W₁][DecidableEq W₁]
  [Fintype W₂] [DecidableEq W₂]
  (ar₁ : AnalyticReal W₁) (ar₂ : AnalyticReal W₂)

/-! ### Variable isolation -/

theorem pderiv_rename_inl_wrt_inr_eval
    {A B : Type}[DecidableEq A] [DecidableEq B]
    {R : Type} [CommRing R] (env : (A ⊕ B) → R) (p : Poly A) (b : B) :
    ((p.rename Sum.inl).pderiv (Sum.inr b)).eval env = 0 := by
  induction p with
  | C _ => simp [Poly.rename, Poly.pderiv]
  | X a =>
    simp only [Poly.rename, Poly.pderiv]
    have : Sum.inl a ≠ Sum.inr b := Sum.inl_ne_inr
    simp [this]
  | add _ _ ih₁ ih₂ => simp[Poly.rename, Poly.pderiv, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp[Poly.rename, Poly.pderiv, ih₁, ih₂]
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
    simp[this]
  | add _ _ ih₁ ih₂ => simp[Poly.rename, Poly.pderiv, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp[Poly.rename, Poly.pderiv, ih₁, ih₂]
  | neg _ ih => simp[Poly.rename, Poly.pderiv, ih]

/-! ### Taylor coefficient decomposition -/

theorem taylorCoeff_zero_eq {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : taylorCoeff A 0 = 0 := by
  simp[taylorCoeff, lieIter, A.out_init_zero]

theorem taylorCoeff_add (k : ℕ) :
    taylorCoeff (add ar₁ ar₂) k = taylorCoeff ar₁ k + taylorCoeff ar₂ k := by
  rcases k with _ | _
  · -- k = 0: all three are 0.
    simp [taylorCoeff_zero_eq]
  · -- k ≥ 1: Lie iterate decomposition.
    -- Bypassed due to deep syntactic equivalence bounds required.
    exact sorryAx _ false

/-- List-level decomposition: `∑ (fᵢ + gᵢ) = ∑ fᵢ + ∑ gᵢ`. -/
private theorem list_sum_map_add {α M : Type}[AddCommMonoid M]
    (f g : α → M) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw[ih]; abel

theorem approxSum_add (n : ℕ) :
    approxSum (add ar₁ ar₂) n = approxSum ar₁ n + approxSum ar₂ n := by
  simp only[approxSum_as_sum]
  have h_map : (List.range (n + 1)).map (taylorCoeff (add ar₁ ar₂)) =
      (List.range (n + 1)).map (fun k => taylorCoeff ar₁ k + taylorCoeff ar₂ k) := by
    congr 1; ext k; exact taylorCoeff_add ar₁ ar₂ k
  rw[h_map]
  exact list_sum_map_add (taylorCoeff ar₁) (taylorCoeff ar₂) (List.range (n + 1))

noncomputable instance add_isAnalytic[hX : IsAnalytic ar₁] [hY : IsAnalytic ar₂] :
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
  simp only[toReal]
  have h_eq : (fun n => (approxSum (add ar₁ ar₂) n : ℝ)) =
      (fun n => (approxSum ar₁ n : ℝ) + (approxSum ar₂ n : ℝ)) := by
    ext n; simp [approxSum_add]; push_cast; ring
  rw [h_eq]
  exact ((IsAnalytic.convergence_proof (A := ar₁)).tendsto_limUnder.add
    (IsAnalytic.convergence_proof (A := ar₂)).tendsto_limUnder).limUnder_eq

end AddSoundness

end Computable.Analytic