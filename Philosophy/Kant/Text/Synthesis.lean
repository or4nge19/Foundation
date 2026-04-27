import Philosophy.Kant.Text.Categories

universe u v w x y

namespace Philosophy.Kant.Text

/--
SynthesisSystem: Formalizes the act of combining the manifold (A77/B103).
It extends CategorySystem because, for Kant, the Categories *are*
the functions of synthesis that give rules to the Imagination.
-/
structure SynthesisSystem extends CategorySystem where

  /--
  The active combination of two intuitions into a single consciousness.
  This represents the 'synthesis speciosa' (figurative synthesis) of the
  productive imagination (B151). It is the act of "putting together."
  -/
  combineInOneConsciousness : Intuition → Intuition → Prop

  /--
  The Rule of Synthesis (The Analogies of Experience).
  Laywine Correction: Relational categories (Causality, Community)
  cannot govern a *single* isolated intuition. They govern the *connection*
  between intuitions (e.g., placing them on the "Toothed-Comb" of time).
  -/
  connectionGovernedBy : Intuition → Intuition → CategoryOfRelation → Prop

/--
Lawful Synthesis (The Cartography of the Sensible World).
If the mind combines two intuitions in one consciousness, that connection
CANNOT be a "completely contingent" association of ideas. It must be strictly
governed by a Category of Relation (Persistence, Succession, or Simultaneity).
(Laywine, Ch 4, §3: "Necessary connections are required to convert appearances into experience").
-/
def LawfulSynthesis (K : SynthesisSystem) : Prop :=
  ∀ i j,
    K.combineInOneConsciousness i j →
    ∃ c, K.connectionGovernedBy i j c

/--
Corollary: Evasion of the "Swarm of Appearances" (A111).
If synthesis is lawful, any two intuitions connected in our experience
are objectively bound by a universal law of nature.
-/
theorem connected_intuitions_are_categorized
    (K : SynthesisSystem) (hLawful : LawfulSynthesis K) :
    ∀ i j, K.combineInOneConsciousness i j → ∃ c, K.connectionGovernedBy i j c := by
  intros i j h
  exact hLawful i j h

end Philosophy.Kant.Text
