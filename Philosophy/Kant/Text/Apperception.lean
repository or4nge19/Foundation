import Philosophy.Kant.Text.Synthesis

universe u v w x y

namespace Philosophy.Kant.Text

/--
The "I think" must be able to accompany all my representations (B131).
An intuition is unified if its combination with any other intuition
is governed by a universal relational rule (category).
-/
def UnifiedInOneConsciousness (K : SynthesisSystem) (i : K.Intuition) : Prop :=
  ∀ j,
    K.combineInOneConsciousness i j →
    ∃ c, K.connectionGovernedBy i j c

/--
The Transcendental Unity of Apperception (TUA).
The supreme principle: ALL intuitions combined in the mind form a single,
law-governed cosmological whole (nature in the formal sense).
-/
def UnityOfApperception (K : SynthesisSystem) : Prop :=
  ∀ i, UnifiedInOneConsciousness K i

theorem unity_of_apperception_implies_common_rule
    {K : SynthesisSystem} (h : UnityOfApperception K)
    {i j : K.Intuition} (hij : K.combineInOneConsciousness i j) :
    ∃ c, K.connectionGovernedBy i j c :=
  h i j hij

theorem lawful_synthesis_preserves_unified_consciousness
    {K : SynthesisSystem} (h : LawfulSynthesis K) :
    UnityOfApperception K := by
  intro i j hij
  exact h i j hij

end Philosophy.Kant.Text
