import Mathlib
/-!
# Posy's Kant: A Formalization of Topological Epistemology

This file formalizes Carl Posy's Kripkean reconstruction of Immanuel Kant's 
Critical Philosophy, specifically targeting the resolution of the Antinomies
and the distinction between Constitutive completeness and Regulative inquiry.
-/

namespace PosyKant

/-! ## 1. Epistemic Frames and the KProp Algebra 
An epistemic frame is a partial order representing the "growth of knowledge".
By relying on `Mathlib.Order.UpperSet`, we get intuitionistic logic 
(a Heyting Algebra) for free. `p ⊔ q` is intuitionistic OR, and `pᶜ` is 
intuitionistic NOT (the pseudo-complement).
-/

abbrev PosyFrame := Type

/-- 
KProp is the set of warranted propositions. 
In Lean 4, `UpperSet` automatically handles monotonicity:
if a proposition is warranted at `w`, it remains warranted at all `w' ≥ w`.
-/
abbrev KProp (F : PosyFrame) [Preorder F] := UpperSet F

/-! ## 2. The Philosophical Standpoints 
We formalize Kant's "Standpoints" as topological constraints on the Kripke frame.
-/

/-- Transcendental Realism (Dogmatism): The frame collapses into a single "God's Eye" node. 
    Knowledge does not "grow"; the world is statically given as a whole. -/
class Standpoint.Dogmatism (F : PosyFrame) [Preorder F] : Prop where
  static : ∀ w w' : F, w ≤ w'

/-- Transcendental Idealism (The Understanding): We are finite and receptive. 
    There is no ultimate, final state of empirical knowledge. -/
class Standpoint.Receptivity (F : PosyFrame) [Preorder F] : Prop where
  always_more : ∀ w : F, ∃ w', w < w'

/-- 
Theorem: Transcendental Realism inevitably forces Classical Logic (Bivalence).
If we adopt the Dogmatist standpoint, the Law of Excluded Middle holds everywhere.
-/
theorem realist_is_classical {F : PosyFrame} [Preorder F][Standpoint.Dogmatism F] 
    (p : KProp F) (w : F) : w ∈ p ⊔ pᶜ := by
  -- In a Heyting Algebra of UpperSets, `w ∈ pᶜ` reduces to `∀ w' ≥ w, w' ∉ p`
  by_cases h : w ∈ p
  · exact Or.inl h
  · right
    intro w' _
    -- Because the frame is static, w' must be structurally identical to w
    have hw' : w' ≤ w := Standpoint.Dogmatism.static w' w
    intro hw'p
    -- Monotonicity backwards yields contradiction
    exact h (p.up' hw' hw'p)

/-! ## 3. Transcendent Free Logic 
To handle empirical objects (like the Carpenter's Table), the domain of known 
objects must grow monotonically with the frame.
-/

structure KripkeModel (F : PosyFrame) [Preorder F] (U : Type) where
  domain : F → Set U
  mono   : ∀ {w w'}, w ≤ w' → domain w ⊆ domain w'

namespace KripkeModel
variable {F : PosyFrame} [Preorder F] {U : Type} (M : KripkeModel F U)

/-- Existential: The object must exist in our *current* epistemic domain. -/
def Ex (P : U → KProp F) : KProp F where
  carrier := { w | ∃ x ∈ M.domain w, w ∈ P x }
  up' := fun w₁ w₂ h_le ⟨x, hx_dom, hx_P⟩ => 
    ⟨x, M.mono h_le hx_dom, (P x).up' h_le hx_P⟩

/-- Universal: The property must hold for all objects discovered *now and in the future*. -/
def All (P : U → KProp F) : KProp F where
  carrier := { w | ∀ w' ≥ w, ∀ x ∈ M.domain w', w' ∈ P x }
  up' := fun w₁ w₂ h_le h_all w₃ hw23 x hx => 
    h_all w₃ (le_trans h_le hw23) x hx

end KripkeModel

/-! ## 4. The Second Antinomy: Spongy Matter
We now build the exact model of Kant's "Ad Infinitum" division of matter.
The frame is `ℕ` (a linear chain of ever-finer microscopic discoveries).
-/

def SpongyFrame := ℕ
instance : Preorder SpongyFrame := inferInstanceAs (Preorder ℕ)

-- The domain at node `n` contains all material parts down to granularity level `n`.
def SpongyPlank : KripkeModel SpongyFrame ℕ where
  domain n := { x | x ≤ n }
  mono h_le x hx := le_trans hx h_le

-- "y is a strictly finer component than x"
def Finer (y x : ℕ) : KProp SpongyFrame where
  carrier := { _w | y > x }
  up' := fun _ _ _ h => h

section AntinomyProofs
open KripkeModel 

/-- The Dogmatic Thesis: "There exists an ultimate simple part of matter."
    Formalized: There is an x such that for all y, y is not finer than x. -/
def Thesis : KProp SpongyFrame :=
  SpongyPlank.Ex fun x => SpongyPlank.All fun y => (Finer y x)ᶜ

/-- The Dogmatic Antithesis: "The object is actually an infinite telescoping sum of parts."
    Formalized: For every x, we *already possess* a y that is finer than x. -/
def Antithesis : KProp SpongyFrame :=
  SpongyPlank.All fun x => SpongyPlank.Ex fun y => Finer y x

/-- Kant's Resolution: The Regulative Push.
    "We can never rest with any found division."
    Formalized: The Double Negation of the Antithesis. -/
def RegulativePush : KProp SpongyFrame :=
  SpongyPlank.All fun x => ((SpongyPlank.Ex fun y => Finer y x)ᶜ)ᶜ

/-- 
THEOREM 1: The Thesis is false everywhere. 
We never find a true atom, because matter is spongy.
-/
theorem thesis_is_empty (n : SpongyFrame) : n ∉ Thesis := by
  intro ⟨x, _, hx⟩
  -- hx : ∀ w' ≥ n, ∀ y ≤ w', w' ∈ (Finer y x)ᶜ
  let w_future := max n (x + 1)
  have hw_future : w_future ≥ n := le_max_left n (x + 1)
  have h_contra := hx w_future hw_future (x + 1) (le_max_right n (x + 1))
  -- h_contra means that ∀ w'' ≥ w_future, ¬ (x + 1 > x)
  apply h_contra w_future (le_refl w_future)
  omega

/-- 
THEOREM 2: The Antithesis is false everywhere.
We never actually *have* the completed infinite sum of parts at any finite node.
-/
theorem antithesis_is_empty (n : SpongyFrame) : n ∉ Antithesis := by
  intro h
  -- h : ∀ w' ≥ n, ∀ x ≤ w', ∃ y ≤ w', y > x
  -- Evaluate at w' = n, x = n
  have ⟨y, hy_dom, hy_finer⟩ := h n (le_refl n) n (le_refl n)
  omega

/-- 
THEOREM 3: The Regulative Push is TRUE everywhere!
Even though the infinite division doesn't exist *now* (Antithesis is false), 
we can logically guarantee that the search will never hit a dead end.
This formally vindicates Posy's Kant: Double Negation is valid, but Excluded Middle is not.
-/
theorem regulative_push_is_universal (n : SpongyFrame) : n ∈ RegulativePush := by
  intro n' _ x _ hn'
  -- hn' is the assumption that the search hits a dead end
  -- hn' : ∀ w'' ≥ n', ¬(∃ y ≤ w'', y > x)
  -- We must show a contradiction by finding a future node and a finer part.
  let w'' := max n' (x + 1)
  have hw'' : w'' ≥ n' := le_max_left n' (x + 1)
  apply hn' w'' hw''
  use (x + 1)
  exact ⟨le_max_right n' (x + 1), by omega⟩

end AntinomyProofs

/-! ## 5. Peircean Truth vs. The Carpenter's Table
You asked: "If I build a table, isn't it complete (a maximal set of sentences)?"
Posy answers: Yes, empirically it is completely domesticated. 
But transcendentally, if we view truth as "Eventual Assertability in the infinite limit" 
(Peircean Truth), it inevitably collapses into Dogmatic Bivalence.
-/

/-- 
Peircean Truth: A proposition is true if it eventually becomes warranted and stays warranted.

TOPOLOGICAL NOTE ON BRANCHING vs. LINEAR FRAMES:
Defining Peircean Truth via simple existential quantification (`∃ w, w ∈ p`) 
implicitly assumes a directed or linear frame (like `SpongyFrame` / `ℕ`), capturing 
Posy's *ad infinitum* distinction. 

As Posy notes, the 1st Antinomy (Spatial Extent) operates *ad indefinitum*, 
meaning the frame is a branching tree. In a branching frame, `∃ w, w ∈ p` only 
means there is *some* possible future path where `p` is discovered, not that its 
discovery is *inevitable* across all paths. To strictly formalize Peircean inevitability 
on branching frames, one would require evaluation over maximal chains or filters. 
However, for linear epistemic growth (like empirical observation sequences), 
this existential formulation perfectly captures Peirce's "fullness of time".
-/
def PeirceanTrue {F : PosyFrame} [Preorder F] (p : KProp F) : Prop :=
  ∃ w : F, w ∈ p

/-- 
THEOREM 4: Why Kant rejects Peircean Truth for the Empirical Object.
If we accept Peircean Truth as our semantic standard, we are forced back into 
Classical Bivalence, destroying the Critical Philosophy.
-/
theorem peircean_collapses_to_bivalence {F : PosyFrame}[Preorder F] [Nonempty F] 
    (p : KProp F) : PeirceanTrue p ∨ PeirceanTrue pᶜ := by
  by_cases h : ∃ w, w ∈ p
  · exact Or.inl h
  · right
    -- If p is never warranted anywhere, then pᶜ is warranted everywhere!
    push_neg at h
    obtain ⟨w₀⟩ := ‹Nonempty F›
    use w₀
    intro w' _
    exact h w'

/-- 
The Carpenter's Table (Constitutive Empirical Completeness):
A macroscopic property P of the table is "Observable" if it is decidable 
for all currently constructed objects. In the empirical project, the table 
IS a complete Bolzanian object with respect to these properties.
-/
def IsMacroscopicallyComplete {F : PosyFrame} [Preorder F] {U : Type} 
    (M : KripkeModel F U) (Table_Color : U → KProp F) : Prop :=
  ∀ w : F, ∀ x ∈ M.domain w, w ∈ (Table_Color x) ⊔ (Table_Color x)ᶜ

end PosyKant