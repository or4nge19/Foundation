import Philosophy.Aristotle.PriorAnalytics.ProofTheory

namespace Aristotle.PriorAnalytics

/-!
# Chain and Route Scaffolding

This module isolates the current chain/route bookkeeping away from the core
syntax and proof theory. It remains available to downstream modules while the
regress analysis is rebuilt on a less stipulative basis.
-/

/--
A semantic chain of terms ordered through intermediate predications.

Unlike `TermChain`, this is not proof-search bookkeeping. It is the kind of
acyclic term-structure a Smith-style regress argument reasons about.
-/
structure PredicationChain where
  upper : Term
  lower : Term
  middles : List Term
  noCycles : (upper :: middles ++ [lower]).Nodup

def PredicationChain.terms : PredicationChain → List Term
  | ⟨upper, lower, middles, _⟩ => upper :: middles ++ [lower]

def PredicationChain.conclusion (chain : PredicationChain) : Categorical :=
  .A chain.lower chain.upper

def PredicationChain.depth (chain : PredicationChain) : Nat :=
  chain.middles.length

/--
An Aristotelian term-chain records the successive insertion of middle terms
between two extremes in a universal affirmative proof-search.
-/
structure TermChain where
  upper : Term
  lower : Term
  middles : List Term

/--
Universal-negative route scaffolding built from one negative premise together
with an affirmative support-chain.
-/
inductive NegativeRoute
  | celarent (predicate : Term) (support : TermChain)
  | cesare (predicate : Term) (support : TermChain)
  | camestres (subject : Term) (support : TermChain)

/--
Route bookkeeping for direct figured arguments, affirmative chains, and
negative routes.
-/
inductive ProofRoute
  | figured (syllogism : FiguredSyllogism)
  | chain (chain : TermChain)
  | negative (route : NegativeRoute)

inductive RouteKind
  | direct
  | chain
  | negative
  deriving DecidableEq, Repr

def TermChain.terms : TermChain → List Term
  | ⟨upper, lower, []⟩ => [upper, lower]
  | ⟨upper, lower, middle :: rest⟩ => upper :: TermChain.terms ⟨middle, lower, rest⟩

def TermChain.premises : TermChain → List Categorical
  | ⟨upper, lower, []⟩ => [Categorical.A lower upper]
  | ⟨upper, lower, middle :: rest⟩ =>
      Categorical.A middle upper :: TermChain.premises ⟨middle, lower, rest⟩

def TermChain.conclusion (chain : TermChain) : Categorical :=
  Categorical.A chain.lower chain.upper

def TermChain.length (chain : TermChain) : Nat :=
  chain.terms.length

def TermChain.depth (chain : TermChain) : Nat :=
  chain.middles.length

def TermChain.insertBelowTop (chain : TermChain) (middle : Term) : TermChain :=
  ⟨chain.upper, chain.lower, middle :: chain.middles⟩

/--
Proof-search chains may fail to be faithful semantic chains when middle terms
repeat. This predicate isolates the well-formed cases that can be re-read as
acyclic semantic chains.
-/
def TermChain.WellFormed (chain : TermChain) : Prop :=
  chain.terms.Nodup

theorem TermChain.terms_eq_append (chain : TermChain) :
    chain.terms = chain.upper :: chain.middles ++ [chain.lower] := by
  cases chain with
  | mk upper lower middles =>
      induction middles generalizing upper with
      | nil =>
          simp [TermChain.terms]
      | cons middle rest ih =>
          simp [TermChain.terms, ih]

def TermChain.toPredicationChain (chain : TermChain)
    (h : chain.WellFormed) : PredicationChain :=
  { upper := chain.upper
    lower := chain.lower
    middles := chain.middles
    noCycles := by
      simpa [PredicationChain.terms, TermChain.WellFormed, chain.terms_eq_append] using h }

def NegativeRoute.depth : NegativeRoute → Nat
  | .celarent _ support => support.depth + 1
  | .cesare _ support => support.depth + 1
  | .camestres _ support => support.depth + 1

def NegativeRoute.negativePremise : NegativeRoute → Categorical
  | .celarent predicate support => Categorical.E support.upper predicate
  | .cesare predicate support => Categorical.E predicate support.upper
  | .camestres subject support => Categorical.E subject support.upper

def NegativeRoute.affirmativePremise : NegativeRoute → Categorical
  | .celarent _ support => support.conclusion
  | .cesare _ support => support.conclusion
  | .camestres _ support => support.conclusion

def NegativeRoute.premises : NegativeRoute → List Categorical
  | .celarent predicate support =>
      NegativeRoute.negativePremise (.celarent predicate support) :: support.premises
  | .cesare predicate support =>
      NegativeRoute.negativePremise (.cesare predicate support) :: support.premises
  | .camestres subject support =>
      support.premises ++ [NegativeRoute.negativePremise (.camestres subject support)]

def NegativeRoute.conclusion : NegativeRoute → Categorical
  | .celarent predicate support => Categorical.E support.lower predicate
  | .cesare predicate support => Categorical.E support.lower predicate
  | .camestres subject support => Categorical.E subject support.lower

def ProofRoute.premises : ProofRoute → List Categorical
  | .figured syllogism => [FiguredSyllogism.majorPremise syllogism, FiguredSyllogism.minorPremise syllogism]
  | .chain routeChain => TermChain.premises routeChain
  | .negative negativeRoute => NegativeRoute.premises negativeRoute

def ProofRoute.conclusion : ProofRoute → Categorical
  | .figured syllogism => FiguredSyllogism.conclusion syllogism
  | .chain routeChain => TermChain.conclusion routeChain
  | .negative negativeRoute => NegativeRoute.conclusion negativeRoute

def ProofRoute.isDirect : ProofRoute → Prop
  | .figured _ => True
  | .chain _ => False
  | .negative _ => False

def ProofRoute.isNegative : ProofRoute → Prop
  | .negative _ => True
  | _ => False

def ProofRoute.isChain : ProofRoute → Prop
  | .chain _ => True
  | _ => False

def ProofRoute.kind : ProofRoute → RouteKind
  | .figured _ => .direct
  | .chain _ => .chain
  | .negative _ => .negative

def ProofRoute.depth : ProofRoute → Nat
  | .figured _ => 0
  | .chain routeChain => routeChain.depth + 1
  | .negative negativeRoute => negativeRoute.depth

/--
A bookkeeping depth bound on a route.

This is kept only for downstream compatibility; it is not the substantive
termination thesis Smith argues for in the *Posterior Analytics*.
-/
def ProofRoute.TerminatesWithin (route : ProofRoute) (bound : Nat) : Prop :=
  route.depth ≤ bound

theorem termChain_premises_ne_nil (chain : TermChain) : chain.premises ≠ [] := by
  cases chain with
  | mk upper lower middles =>
      cases middles <;> simp [TermChain.premises]

theorem negativeRoute_premises_ne_nil (route : NegativeRoute) : route.premises ≠ [] := by
  cases route with
  | celarent predicate support =>
      simp [NegativeRoute.premises, NegativeRoute.negativePremise]
  | cesare predicate support =>
      simp [NegativeRoute.premises, NegativeRoute.negativePremise]
  | camestres subject support =>
      simp [NegativeRoute.premises, NegativeRoute.negativePremise]

theorem proofRoute_premises_ne_nil (route : ProofRoute) : route.premises ≠ [] := by
  cases route with
  | figured syllogism =>
      simp [ProofRoute.premises]
  | chain routeChain =>
      simpa [ProofRoute.premises] using termChain_premises_ne_nil routeChain
  | negative negativeRoute =>
      simpa [ProofRoute.premises] using negativeRoute_premises_ne_nil negativeRoute

theorem termChain_terms_length_eq_premises_length_succ (chain : TermChain) :
    chain.terms.length = chain.premises.length + 1 := by
  cases chain with
  | mk upper lower middles =>
      induction middles generalizing upper with
      | nil =>
          simp [TermChain.terms, TermChain.premises]
      | cons middle rest ih =>
          simp [TermChain.terms, TermChain.premises, ih, Nat.add_comm] at *

theorem termChain_length_pos (chain : TermChain) : 0 < chain.length := by
  have h : chain.length = chain.premises.length + 1 := by
    simpa [TermChain.length] using termChain_terms_length_eq_premises_length_succ chain
  rw [h]
  exact Nat.succ_pos _

theorem termChain_depth_lt_length (chain : TermChain) : chain.depth < chain.length := by
  cases chain with
  | mk upper lower middles =>
      induction middles generalizing upper with
      | nil =>
          simp [TermChain.depth, TermChain.length, TermChain.terms]
      | cons middle rest ih =>
          have htail : (TermChain.mk middle lower rest).depth <
              (TermChain.mk middle lower rest).length :=
            ih (upper := middle)
          have htail' : rest.length < (TermChain.mk middle lower rest).terms.length := by
            simpa [TermChain.depth, TermChain.length] using htail
          simpa [TermChain.depth, TermChain.length, TermChain.terms] using htail'

theorem termChain_derives_conclusion (chain : TermChain) :
    Derives chain.premises chain.conclusion := by
  cases chain with
  | mk upper lower middles =>
      induction middles generalizing upper with
      | nil =>
          exact Derives.premise (by simp [TermChain.premises, TermChain.conclusion])
      | cons middle rest ih =>
          have hmajor : Derives (TermChain.premises ⟨upper, lower, middle :: rest⟩)
              (Categorical.A middle upper) := by
            exact Derives.premise (by simp [TermChain.premises])
          have htail : Derives (TermChain.premises ⟨middle, lower, rest⟩)
              (Categorical.A lower middle) :=
            ih (upper := middle)
          have htail' : Derives (TermChain.premises ⟨upper, lower, middle :: rest⟩)
              (Categorical.A lower middle) := by
            exact Derives.monotone (premises := TermChain.premises ⟨middle, lower, rest⟩)
              (premises' := TermChain.premises ⟨upper, lower, middle :: rest⟩)
              (conclusion := Categorical.A lower middle)
              (fun hmem => by simp [TermChain.premises, hmem]) htail
          simpa [TermChain.conclusion] using
            Derives.binary hmajor htail' (Deduce.Barbara lower middle upper)

theorem negativeRoute_derives_conclusion (route : NegativeRoute) :
    Derives route.premises route.conclusion := by
  cases route with
  | celarent predicate support =>
      have hneg :
          Derives (NegativeRoute.negativePremise (.celarent predicate support) :: support.premises)
            (NegativeRoute.negativePremise (.celarent predicate support)) := by
        exact Derives.premise (by simp [NegativeRoute.negativePremise])
      have hsup :
          Derives (NegativeRoute.negativePremise (.celarent predicate support) :: support.premises)
            support.conclusion := by
        exact Derives.monotone
          (premises := support.premises)
          (premises' := NegativeRoute.negativePremise (.celarent predicate support) :: support.premises)
          (conclusion := support.conclusion)
          (fun hmem => by simp [hmem])
          (termChain_derives_conclusion support)
      simpa [NegativeRoute.premises, NegativeRoute.conclusion, NegativeRoute.negativePremise,
        TermChain.conclusion] using
        Derives.binary hneg hsup (Deduce.Celarent support.lower support.upper predicate)
  | cesare predicate support =>
      have hneg :
          Derives (NegativeRoute.negativePremise (.cesare predicate support) :: support.premises)
            (NegativeRoute.negativePremise (.cesare predicate support)) := by
        exact Derives.premise (by simp [NegativeRoute.negativePremise])
      have hsup :
          Derives (NegativeRoute.negativePremise (.cesare predicate support) :: support.premises)
            support.conclusion := by
        exact Derives.monotone
          (premises := support.premises)
          (premises' := NegativeRoute.negativePremise (.cesare predicate support) :: support.premises)
          (conclusion := support.conclusion)
          (fun hmem => by simp [hmem])
          (termChain_derives_conclusion support)
      simpa [NegativeRoute.premises, NegativeRoute.conclusion, NegativeRoute.negativePremise,
        TermChain.conclusion] using
        Derives.binary hneg hsup (Deduce.Cesare support.lower support.upper predicate)
  | camestres subject support =>
      have hsup :
          Derives (support.premises ++ [NegativeRoute.negativePremise (.camestres subject support)])
            support.conclusion := by
        exact Derives.monotone
          (premises := support.premises)
          (premises' := support.premises ++ [NegativeRoute.negativePremise (.camestres subject support)])
          (conclusion := support.conclusion)
          (fun hmem => by simp [hmem])
          (termChain_derives_conclusion support)
      have hneg :
          Derives (support.premises ++ [NegativeRoute.negativePremise (.camestres subject support)])
            (NegativeRoute.negativePremise (.camestres subject support)) := by
        exact Derives.premise (by simp [NegativeRoute.negativePremise])
      simpa [NegativeRoute.premises, NegativeRoute.conclusion, NegativeRoute.negativePremise,
        TermChain.conclusion] using
        Derives.binary hsup hneg (Deduce.Camestres subject support.upper support.lower)

theorem proofRoute_derives (route : ProofRoute) :
    Derives route.premises route.conclusion := by
  cases route with
  | figured syllogism =>
      simpa [ProofRoute.premises, ProofRoute.conclusion] using figuredSyllogism_derives syllogism
  | chain routeChain =>
      simpa [ProofRoute.premises, ProofRoute.conclusion] using termChain_derives_conclusion routeChain
  | negative negativeRoute =>
      simpa [ProofRoute.premises, ProofRoute.conclusion] using negativeRoute_derives_conclusion negativeRoute

theorem proofRoute_figured_isDirect (syllogism : FiguredSyllogism) :
    (ProofRoute.figured syllogism).isDirect := by
  simp [ProofRoute.isDirect]

theorem proofRoute_chain_conclusion_is_affirmative (chain : TermChain) :
    ∃ S P, (ProofRoute.chain chain).conclusion = Categorical.A S P := by
  exact ⟨chain.lower, chain.upper, by simp [ProofRoute.conclusion, TermChain.conclusion]⟩

theorem negativeRoute_conclusion_is_negative (route : NegativeRoute) :
    ∃ S P, route.conclusion = Categorical.E S P := by
  cases route with
  | celarent predicate support => exact ⟨support.lower, predicate, rfl⟩
  | cesare predicate support => exact ⟨support.lower, predicate, rfl⟩
  | camestres subject support => exact ⟨subject, support.lower, rfl⟩

theorem proofRoute_isChain_conclusion_is_affirmative (route : ProofRoute)
    (hchain : route.isChain) :
    ∃ S P, route.conclusion = Categorical.A S P := by
  cases route with
  | figured syllogism => cases hchain
  | chain chain =>
      simpa [ProofRoute.isChain] using proofRoute_chain_conclusion_is_affirmative chain
  | negative negativeRoute => cases hchain

theorem proofRoute_isNegative_conclusion_is_negative (route : ProofRoute)
    (hnegative : route.isNegative) :
    ∃ S P, route.conclusion = Categorical.E S P := by
  cases route with
  | figured syllogism => cases hnegative
  | chain chain => cases hnegative
  | negative negativeRoute =>
      simpa [ProofRoute.isNegative, ProofRoute.conclusion] using
        negativeRoute_conclusion_is_negative negativeRoute

theorem negativeRoute_depth_pos (route : NegativeRoute) : 0 < route.depth := by
  cases route <;> simp [NegativeRoute.depth]

theorem proofRoute_depth_pos_of_chain (chain : TermChain) :
    0 < (ProofRoute.chain chain).depth := by
  simp [ProofRoute.depth]

theorem proofRoute_isChain_depth_pos (route : ProofRoute)
    (hchain : route.isChain) :
    0 < route.depth := by
  cases route with
  | figured syllogism => cases hchain
  | chain chain => simpa [ProofRoute.isChain] using proofRoute_depth_pos_of_chain chain
  | negative negativeRoute => cases hchain

theorem proofRoute_isNegative_depth_pos (route : ProofRoute)
    (hnegative : route.isNegative) :
    0 < route.depth := by
  cases route with
  | figured syllogism => cases hnegative
  | chain chain => cases hnegative
  | negative negativeRoute =>
      simpa [ProofRoute.isNegative, ProofRoute.depth] using negativeRoute_depth_pos negativeRoute

theorem proofRoute_isNegative_not_direct (route : ProofRoute)
    (hnegative : route.isNegative) :
    ¬ route.isDirect := by
  cases route <;> simp [ProofRoute.isNegative, ProofRoute.isDirect] at hnegative ⊢

theorem proofRoute_not_direct_iff_isChain_or_isNegative (route : ProofRoute) :
    ¬ route.isDirect ↔ route.isChain ∨ route.isNegative := by
  cases route with
  | figured syllogism =>
      simp [ProofRoute.isDirect, ProofRoute.isChain, ProofRoute.isNegative]
  | chain chain =>
      simp [ProofRoute.isDirect, ProofRoute.isChain, ProofRoute.isNegative]
  | negative negativeRoute =>
      simp [ProofRoute.isDirect, ProofRoute.isChain, ProofRoute.isNegative]

theorem proofRoute_terminates (route : ProofRoute) : route.TerminatesWithin route.depth := by
  exact le_rfl

theorem proofRoute_direct_iff_depth_zero (route : ProofRoute) :
    route.isDirect ↔ route.depth = 0 := by
  cases route with
  | figured syllogism => simp [ProofRoute.isDirect, ProofRoute.depth]
  | chain routeChain =>
      simp [ProofRoute.isDirect, ProofRoute.depth, TermChain.depth]
  | negative negativeRoute =>
      have hne : negativeRoute.depth ≠ 0 := Nat.ne_of_gt (negativeRoute_depth_pos negativeRoute)
      simp [ProofRoute.isDirect, ProofRoute.depth, hne]

theorem proofRoute_not_direct_of_positive_depth (route : ProofRoute)
    (hdepth : 0 < route.depth) :
    ¬ route.isDirect := by
  intro hdirect
  have hzero : route.depth = 0 := (proofRoute_direct_iff_depth_zero route).1 hdirect
  exact Nat.ne_of_gt hdepth hzero

theorem proofRoute_classification (route : ProofRoute) :
    (route.kind = .direct ∧ route.isDirect ∧ route.depth = 0) ∨
    (route.kind = .chain ∧ route.isChain ∧ 0 < route.depth ∧
      ∃ S P, route.conclusion = Categorical.A S P) ∨
    (route.kind = .negative ∧ route.isNegative ∧ 0 < route.depth ∧
      ∃ S P, route.conclusion = Categorical.E S P) := by
  cases route with
  | figured syllogism =>
      left
      simp [ProofRoute.kind, ProofRoute.isDirect, ProofRoute.depth]
  | chain chain =>
      right
      left
      refine ⟨by simp [ProofRoute.kind], by simp [ProofRoute.isChain],
        proofRoute_depth_pos_of_chain chain, ?_⟩
      exact proofRoute_chain_conclusion_is_affirmative chain
  | negative negativeRoute =>
      right
      right
      refine ⟨by simp [ProofRoute.kind], by simp [ProofRoute.isNegative],
        by simpa [ProofRoute.depth] using negativeRoute_depth_pos negativeRoute, ?_⟩
      simpa [ProofRoute.conclusion] using negativeRoute_conclusion_is_negative negativeRoute

end Aristotle.PriorAnalytics
