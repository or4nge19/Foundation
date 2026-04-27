import Philosophy.Aristotle.PriorAnalytics.Chains

namespace Aristotle.PriorAnalytics

/-!
# Premise Regress

Robin Smith describes a premise regress as a sequence of premise-stocks obtained
by repeatedly replacing one proposition with premises from which it follows.

This module implements that replacement relation for the universal moods that
carry Smith's proof-theoretic regress arguments. It does **not** claim the full
termination result of *Posterior Analytics* I.22. Instead, it gives an honest
constructive account of the finite regresses already represented by
`TermChain` and `NegativeRoute`.
-/

/--
One proof-theoretic replacement step in a premise regress.

The relation records the finite premise patterns Smith isolates for universal
conclusions. Order is only bookkeeping for the premise stock.
-/
structure ExpansionWitness where
  leftCtx : List Categorical
  rightCtx : List Categorical
  subject : Term
  middle : Term
  predicate : Term

/--
A stricter witness for regress expansion that rules out trivial self-middle
steps. This is the witness shape intended for semantic regress arguments.
-/
structure StrictExpansionWitness extends ExpansionWitness where
  middle_ne_subject : middle ≠ subject
  middle_ne_predicate : middle ≠ predicate

def PremiseStockWellFormed (truth : Categorical → Prop)
    (premises : List Categorical) : Prop :=
  premises.Nodup ∧ ∀ ⦃premise : Categorical⦄, premise ∈ premises → truth premise

def BarbaraExpansion (current next : List Categorical) : Prop :=
  ∃ w : ExpansionWitness,
    current = w.leftCtx ++ [Categorical.A w.subject w.predicate] ++ w.rightCtx ∧
    next = w.leftCtx ++ [Categorical.A w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx

def CelarentExpansion (current next : List Categorical) : Prop :=
  ∃ w : ExpansionWitness,
    current = w.leftCtx ++ [Categorical.E w.subject w.predicate] ++ w.rightCtx ∧
    next = w.leftCtx ++ [Categorical.E w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx

def CesareExpansion (current next : List Categorical) : Prop :=
  ∃ w : ExpansionWitness,
    current = w.leftCtx ++ [Categorical.E w.subject w.predicate] ++ w.rightCtx ∧
    next = w.leftCtx ++ [Categorical.E w.predicate w.middle, Categorical.A w.subject w.middle] ++ w.rightCtx

def CamestresExpansion (current next : List Categorical) : Prop :=
  ∃ w : ExpansionWitness,
    current = w.leftCtx ++ [Categorical.E w.subject w.predicate] ++ w.rightCtx ∧
    next = w.leftCtx ++ [Categorical.A w.predicate w.middle, Categorical.E w.subject w.middle] ++ w.rightCtx

def PremiseExpansion (current next : List Categorical) : Prop :=
  BarbaraExpansion current next ∨
  CelarentExpansion current next ∨
  CesareExpansion current next ∨
  CamestresExpansion current next

structure DisciplinedRegressStep (truth : Categorical → Prop) where
  current : List Categorical
  next : List Categorical
  expansion : PremiseExpansion current next
  current_wf : PremiseStockWellFormed truth current
  next_wf : PremiseStockWellFormed truth next

structure AcyclicPremiseRegress (truth : Categorical → Prop) where
  stocks : List (List Categorical)
  noCycles : stocks.Nodup
  wellFormed : ∀ ⦃stock : List Categorical⦄, stock ∈ stocks → PremiseStockWellFormed truth stock

theorem premiseExpansion_barbara (leftCtx rightCtx : List Categorical) (S M P : Term) :
    PremiseExpansion
      (leftCtx ++ [Categorical.A S P] ++ rightCtx)
      (leftCtx ++ [Categorical.A M P, Categorical.A S M] ++ rightCtx) :=
  Or.inl ⟨{
    leftCtx := leftCtx
    rightCtx := rightCtx
    subject := S
    middle := M
    predicate := P
  }, rfl, rfl⟩

theorem premiseExpansion_celarent (leftCtx rightCtx : List Categorical) (S M P : Term) :
    PremiseExpansion
      (leftCtx ++ [Categorical.E S P] ++ rightCtx)
      (leftCtx ++ [Categorical.E M P, Categorical.A S M] ++ rightCtx) :=
  Or.inr <| Or.inl ⟨{
    leftCtx := leftCtx
    rightCtx := rightCtx
    subject := S
    middle := M
    predicate := P
  }, rfl, rfl⟩

theorem premiseExpansion_cesare (leftCtx rightCtx : List Categorical) (S M P : Term) :
    PremiseExpansion
      (leftCtx ++ [Categorical.E S P] ++ rightCtx)
      (leftCtx ++ [Categorical.E P M, Categorical.A S M] ++ rightCtx) :=
  Or.inr <| Or.inr <| Or.inl ⟨{
    leftCtx := leftCtx
    rightCtx := rightCtx
    subject := S
    middle := M
    predicate := P
  }, rfl, rfl⟩

theorem premiseExpansion_camestres (leftCtx rightCtx : List Categorical) (S M P : Term) :
    PremiseExpansion
      (leftCtx ++ [Categorical.E S P] ++ rightCtx)
      (leftCtx ++ [Categorical.A P M, Categorical.E S M] ++ rightCtx) :=
  Or.inr <| Or.inr <| Or.inr ⟨{
    leftCtx := leftCtx
    rightCtx := rightCtx
    subject := S
    middle := M
    predicate := P
  }, rfl, rfl⟩

theorem premiseExpansion_length_eq_succ {current next : List Categorical}
    (h : PremiseExpansion current next) :
    next.length = current.length + 1 := by
  rcases h with h | h | h | h
  · rcases h with ⟨w, rfl, rfl⟩
    simp [List.length_append, Nat.add_left_comm, Nat.add_comm]
  · rcases h with ⟨w, rfl, rfl⟩
    simp [List.length_append, Nat.add_left_comm, Nat.add_comm]
  · rcases h with ⟨w, rfl, rfl⟩
    simp [List.length_append, Nat.add_left_comm, Nat.add_comm]
  · rcases h with ⟨w, rfl, rfl⟩
    simp [List.length_append, Nat.add_left_comm, Nat.add_comm]

theorem premiseExpansion_withContext {current next : List Categorical}
    (left right : List Categorical) (h : PremiseExpansion current next) :
    PremiseExpansion (left ++ current ++ right) (left ++ next ++ right) := by
  rcases h with h | h | h | h
  · rcases h with ⟨w, rfl, rfl⟩
    simpa [List.append_assoc] using
      premiseExpansion_barbara (left ++ w.leftCtx) (w.rightCtx ++ right) w.subject w.middle w.predicate
  · rcases h with ⟨w, rfl, rfl⟩
    simpa [List.append_assoc] using
      premiseExpansion_celarent (left ++ w.leftCtx) (w.rightCtx ++ right) w.subject w.middle w.predicate
  · rcases h with ⟨w, rfl, rfl⟩
    simpa [List.append_assoc] using
      premiseExpansion_cesare (left ++ w.leftCtx) (w.rightCtx ++ right) w.subject w.middle w.predicate
  · rcases h with ⟨w, rfl, rfl⟩
    simpa [List.append_assoc] using
      premiseExpansion_camestres (left ++ w.leftCtx) (w.rightCtx ++ right) w.subject w.middle w.predicate

theorem premiseExpansion_replaced_derivable {current next : List Categorical}
    (h : PremiseExpansion current next) :
    ∀ {prop : Categorical}, prop ∈ current → Derives next prop := by
  rcases h with h | h | h | h
  · rcases h with ⟨w, rfl, rfl⟩
    intro prop hmem
    have hcases : prop ∈ w.leftCtx ∨ prop = Categorical.A w.subject w.predicate ∨ prop ∈ w.rightCtx := by
      simpa [List.mem_append, List.mem_cons] using hmem
    rcases hcases with hleft | htarget | hright
    · exact Derives.premise (by simp [List.mem_append, List.mem_cons, hleft])
    · subst prop
      exact Derives.ofDeduce
        (context := w.leftCtx ++ [Categorical.A w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx)
        (fun {premise} hmem => by
          have hpair :
              premise = Categorical.A w.middle w.predicate ∨
                premise = Categorical.A w.subject w.middle := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl <;>
            exact Derives.premise (by simp [List.mem_append, List.mem_cons]))
        (Deduce.Barbara w.subject w.middle w.predicate)
    · have hnext : prop ∈ w.leftCtx ++ [Categorical.A w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx := by
        exact List.mem_append.mpr <| Or.inr (by simp [hright])
      exact Derives.premise hnext
  · rcases h with ⟨w, rfl, rfl⟩
    intro prop hmem
    have hcases : prop ∈ w.leftCtx ∨ prop = Categorical.E w.subject w.predicate ∨ prop ∈ w.rightCtx := by
      simpa [List.mem_append, List.mem_cons] using hmem
    rcases hcases with hleft | htarget | hright
    · exact Derives.premise (by simp [List.mem_append, List.mem_cons, hleft])
    · subst prop
      exact Derives.ofDeduce
        (context := w.leftCtx ++ [Categorical.E w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx)
        (fun {premise} hmem => by
          have hpair :
              premise = Categorical.E w.middle w.predicate ∨
                premise = Categorical.A w.subject w.middle := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl <;>
            exact Derives.premise (by simp [List.mem_append, List.mem_cons]))
        (Deduce.Celarent w.subject w.middle w.predicate)
    · have hnext : prop ∈ w.leftCtx ++ [Categorical.E w.middle w.predicate, Categorical.A w.subject w.middle] ++ w.rightCtx := by
        exact List.mem_append.mpr <| Or.inr (by simp [hright])
      exact Derives.premise hnext
  · rcases h with ⟨w, rfl, rfl⟩
    intro prop hmem
    have hcases : prop ∈ w.leftCtx ∨ prop = Categorical.E w.subject w.predicate ∨ prop ∈ w.rightCtx := by
      simpa [List.mem_append, List.mem_cons] using hmem
    rcases hcases with hleft | htarget | hright
    · exact Derives.premise (by simp [List.mem_append, List.mem_cons, hleft])
    · subst prop
      exact Derives.ofDeduce
        (context := w.leftCtx ++ [Categorical.E w.predicate w.middle, Categorical.A w.subject w.middle] ++ w.rightCtx)
        (fun {premise} hmem => by
          have hpair :
              premise = Categorical.E w.predicate w.middle ∨
                premise = Categorical.A w.subject w.middle := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl <;>
            exact Derives.premise (by simp [List.mem_append, List.mem_cons]))
        (Deduce.Cesare w.subject w.middle w.predicate)
    · have hnext : prop ∈ w.leftCtx ++ [Categorical.E w.predicate w.middle, Categorical.A w.subject w.middle] ++ w.rightCtx := by
        exact List.mem_append.mpr <| Or.inr (by simp [hright])
      exact Derives.premise hnext
  · rcases h with ⟨w, rfl, rfl⟩
    intro prop hmem
    have hcases : prop ∈ w.leftCtx ∨ prop = Categorical.E w.subject w.predicate ∨ prop ∈ w.rightCtx := by
      simpa [List.mem_append, List.mem_cons] using hmem
    rcases hcases with hleft | htarget | hright
    · exact Derives.premise (by simp [List.mem_append, List.mem_cons, hleft])
    · subst prop
      exact Derives.ofDeduce
        (context := w.leftCtx ++ [Categorical.A w.predicate w.middle, Categorical.E w.subject w.middle] ++ w.rightCtx)
        (fun {premise} hmem => by
          have hpair :
              premise = Categorical.A w.predicate w.middle ∨
                premise = Categorical.E w.subject w.middle := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl <;>
            exact Derives.premise (by simp [List.mem_append, List.mem_cons]))
        (Deduce.Camestres w.subject w.middle w.predicate)
    · have hnext : prop ∈ w.leftCtx ++ [Categorical.A w.predicate w.middle, Categorical.E w.subject w.middle] ++ w.rightCtx := by
        exact List.mem_append.mpr <| Or.inr (by simp [hright])
      exact Derives.premise hnext

/--
`RegressesIn n current final` says that `final` is reached from `current`
through exactly `n` premise-expansion steps.
-/
inductive RegressesIn : Nat → List Categorical → List Categorical → Prop where
  | refl (premises : List Categorical) :
      RegressesIn 0 premises premises
  | tail {n : Nat} {current next final : List Categorical} :
      PremiseExpansion current next →
      RegressesIn n next final →
      RegressesIn (n + 1) current final

theorem regressesIn_withContext {n : Nat} {current final : List Categorical}
    (left right : List Categorical) (h : RegressesIn n current final) :
    RegressesIn n (left ++ current ++ right) (left ++ final ++ right) := by
  induction h with
  | refl premises =>
      exact RegressesIn.refl (left ++ premises ++ right)
  | tail hexpand htail ih =>
      exact RegressesIn.tail (premiseExpansion_withContext left right hexpand) ih

theorem regressesIn_trans {m n : Nat} {start middle finish : List Categorical}
    (h₁ : RegressesIn m start middle) (h₂ : RegressesIn n middle finish) :
    RegressesIn (m + n) start finish := by
  induction h₁ generalizing n finish with
  | refl premises =>
      simpa using h₂
  | tail hexpand htail ih =>
      have htail' := ih h₂
      have hindex : _ := RegressesIn.tail hexpand htail'
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hindex

theorem regressesIn_length_eq_add {n : Nat} {start finish : List Categorical}
    (h : RegressesIn n start finish) :
    finish.length = start.length + n := by
  induction h with
  | refl premises =>
      simp
  | tail hexpand htail ih =>
      have hlen := premiseExpansion_length_eq_succ hexpand
      omega

/--
A finite term-chain yields a finite premise regress from its conclusion to its
adjacent-link premises.
-/
theorem termChain_regresses_in_depth (chain : TermChain) :
    RegressesIn chain.depth [chain.conclusion] chain.premises := by
  cases chain with
  | mk upper lower middles =>
      induction middles generalizing upper with
      | nil =>
          simpa [TermChain.depth, TermChain.conclusion, TermChain.premises] using
            RegressesIn.refl [Categorical.A lower upper]
      | cons middle rest ih =>
          have hstep :
              PremiseExpansion
                [Categorical.A lower upper]
                [Categorical.A middle upper, Categorical.A lower middle] := by
            simpa using premiseExpansion_barbara [] [] lower middle upper
          have htail :
              RegressesIn rest.length
                [Categorical.A lower middle]
                (TermChain.premises ⟨middle, lower, rest⟩) :=
            ih (upper := middle)
          have htailCtx :
              RegressesIn rest.length
                [Categorical.A middle upper, Categorical.A lower middle]
                (Categorical.A middle upper :: TermChain.premises ⟨middle, lower, rest⟩) := by
            simpa using regressesIn_withContext [Categorical.A middle upper] [] htail
          simpa [TermChain.depth, TermChain.premises] using
            RegressesIn.tail hstep htailCtx

/--
A negative route likewise yields a finite premise regress from its conclusion to
the stock of premises that support it.
-/
theorem negativeRoute_regresses_in_depth (route : NegativeRoute) :
    RegressesIn route.depth [route.conclusion] route.premises := by
  cases route with
  | celarent predicate support =>
      have hstep :
          PremiseExpansion
            [Categorical.E support.lower predicate]
            [Categorical.E support.upper predicate, Categorical.A support.lower support.upper] := by
        simpa [NegativeRoute.conclusion, NegativeRoute.negativePremise, NegativeRoute.affirmativePremise]
          using premiseExpansion_celarent [] [] support.lower support.upper predicate
      have hchain := termChain_regresses_in_depth support
      have hctx :
          RegressesIn support.depth
            [Categorical.E support.upper predicate, Categorical.A support.lower support.upper]
            (Categorical.E support.upper predicate :: support.premises) := by
        simpa [NegativeRoute.premises, NegativeRoute.negativePremise] using
          regressesIn_withContext [Categorical.E support.upper predicate] [] hchain
      simpa [NegativeRoute.depth] using RegressesIn.tail hstep hctx
  | cesare predicate support =>
      have hstep :
          PremiseExpansion
            [Categorical.E support.lower predicate]
            [Categorical.E predicate support.upper, Categorical.A support.lower support.upper] := by
        simpa [NegativeRoute.conclusion, NegativeRoute.negativePremise, NegativeRoute.affirmativePremise]
          using premiseExpansion_cesare [] [] support.lower support.upper predicate
      have hchain := termChain_regresses_in_depth support
      have hctx :
          RegressesIn support.depth
            [Categorical.E predicate support.upper, Categorical.A support.lower support.upper]
            (Categorical.E predicate support.upper :: support.premises) := by
        simpa [NegativeRoute.premises, NegativeRoute.negativePremise] using
          regressesIn_withContext [Categorical.E predicate support.upper] [] hchain
      simpa [NegativeRoute.depth] using RegressesIn.tail hstep hctx
  | camestres subject support =>
      have hstep :
          PremiseExpansion
            [Categorical.E subject support.lower]
            [Categorical.A support.lower support.upper, Categorical.E subject support.upper] := by
        simpa [NegativeRoute.conclusion, NegativeRoute.negativePremise, NegativeRoute.affirmativePremise]
          using premiseExpansion_camestres [] [] subject support.upper support.lower
      have hchain := termChain_regresses_in_depth support
      have hctx :
          RegressesIn support.depth
            [Categorical.A support.lower support.upper, Categorical.E subject support.upper]
            (support.premises ++ [Categorical.E subject support.upper]) := by
        simpa [NegativeRoute.premises, NegativeRoute.negativePremise] using
          regressesIn_withContext [] [Categorical.E subject support.upper] hchain
      simpa [NegativeRoute.depth, NegativeRoute.premises, NegativeRoute.negativePremise] using
        RegressesIn.tail hstep hctx

/--
A figured syllogism gives the one-step premise regress from conclusion to its
premises.
-/
theorem figuredSyllogism_regresses_in_one_step (f : FiguredSyllogism) :
    RegressesIn 1 [f.conclusion] [f.majorPremise, f.minorPremise] := by
  cases f with
  | mk S M P mood =>
      cases mood
      · simpa using
          RegressesIn.tail (premiseExpansion_barbara [] [] S M P) (RegressesIn.refl _)
      · simpa using
          RegressesIn.tail (premiseExpansion_celarent [] [] S M P) (RegressesIn.refl _)
      · simpa using
          RegressesIn.tail (premiseExpansion_cesare [] [] S M P) (RegressesIn.refl _)
      · simpa using
          RegressesIn.tail (premiseExpansion_camestres [] [] S M P) (RegressesIn.refl _)

/--
The accurate premise-regress length associated with the currently modeled
routes. Direct figured deductions count as one regress step from conclusion to
premises.
-/
def ProofRoute.regressLength : ProofRoute → Nat
  | .figured _ => 1
  | .chain routeChain => routeChain.depth
  | .negative route => route.depth

theorem proofRoute_regresses_in_length (route : ProofRoute) :
    RegressesIn route.regressLength [route.conclusion] route.premises := by
  cases route with
  | figured syllogism =>
      simpa [ProofRoute.regressLength, ProofRoute.conclusion, ProofRoute.premises] using
        figuredSyllogism_regresses_in_one_step syllogism
  | chain chain =>
      simpa [ProofRoute.regressLength, ProofRoute.conclusion, ProofRoute.premises] using
        termChain_regresses_in_depth chain
  | negative route =>
      simpa [ProofRoute.regressLength, ProofRoute.conclusion, ProofRoute.premises] using
        negativeRoute_regresses_in_depth route

end Aristotle.PriorAnalytics
