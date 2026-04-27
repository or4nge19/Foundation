import Mathlib

open CategoryTheory TopologicalSpace Opposite

/-!
# THE CARTOGRAPHY OF THE SENSIBLE WORLD (REVISED)
A Formalization of Laywine's "Cosmology of Experience"

This version addresses:
1. Irreversibility (Time as a Monoid/Poset).
2. The Schematism as a Natural Transformation.
3. The Third Analogy (Community) as a Sheaf-theoretic "Gap Lemma."
-/

section TranscendentalAesthetic

/- 
1. THE ARROW OF TIME (Second Analogy)
Kant argues time is a "succession." Unlike a Group, a Monoid does not 
require inverses, representing the irreversibility of causal events.
-/
variable (Time : Type) [AddMonoid Time] [Preorder Time]

-- The manifold of raw sensory data
variable (Phenomena : Type) [TopologicalSpace Phenomena]

/- 
The World-Process: An additive action of time on phenomena.
`t + p` represents the state `p` after a duration `t`.
-/
variable [AddAction Time Phenomena]

end TranscendentalAesthetic

section TranscendentalLogic

universe u
variable {Locality : Type u} [TopologicalSpace Locality]

/- 
2. THE SCHEMATISM AS A NATURAL TRANSFORMATION
The Schematism is the "third thing" mediating between Intuition and Concepts.
We model this as a Natural Transformation between two functors over the 
topology of experience.
-/

-- A Functor representing the "Passive" reception of data (Intuition)
variable (Intuition : (Opens Locality)ᵒᵖ ⥤ Type u)

-- A Functor representing the "Active" processing of the Understanding (Concepts)
variable (Understanding : (Opens Locality)ᵒᵖ ⥤ Type u)

/--
The Schematism is a rule that assigns to every local patch of intuition 
a conceptual representation, such that the mapping is consistent across 
all nested patches (Naturality).
-/
def Schematism := Intuition ⟶ Understanding

end TranscendentalLogic

section TheAnalogies

variable {Locality : Type u} [TopologicalSpace Locality]
variable (Time : Type) [AddMonoid Time]

/--
3. OBJECTIVE VALIDITY AS EQUIVARIANCE (Second Analogy)
-/
def ObjectiveValidity 
  (synthesis : Phenomena → Phenomena) 
  [AddAction Time Phenomena] : Prop :=
  ∀ (t : Time) (p : Phenomena), synthesis (t +ᵥ p) = t +ᵥ (synthesis p)

/--
4. THE GAP LEMMA: COMMUNITY (Third Analogy)
In modern Mathlib 4, we define a Presheaf as a Functor: `(Opens Locality)ᵒᵖ ⥤ Type u`.
The Sheaf condition is checked against the `grothendieckTopology`.
-/
theorem community_of_experience   
  {Locality : Type u} [TopologicalSpace Locality]  
  (F : TopCat.Sheaf (Type u) (TopCat.of Locality))  
  (U V : Opens Locality)  
  (section_U : F.1.obj (op U))  
  (section_V : F.1.obj (op V))  
  (h_agreement : F.1.map (homOfLE inf_le_left).op section_U =   
                 F.1.map (homOfLE inf_le_right).op section_V) :  
  ∃! (global_object : F.1.obj (op (U ⊔ V))),  
    F.1.map (homOfLE le_sup_left).op global_object = section_U ∧  
    F.1.map (homOfLE le_sup_right).op global_object = section_V := by  
  let ι : Fin 2 → Opens Locality := ![U, V]  
  have sf : ∀ i : Fin 2, F.1.obj (op (ι i)) := ![section_U, section_V]  
  have h_compat : Presheaf.IsCompatible F.1 ι sf := by  
    intro i j  
    fin_cases i <;> fin_cases j <;> simp [sf, ι, h_agreement]  
  exact F.existsUnique_gluing' (U ⊔ V) (fun i => homOfLE (by fin_cases i <;> simp))  
    le_rfl sf h_compat

end TheAnalogies