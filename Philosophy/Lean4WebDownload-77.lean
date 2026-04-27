import Mathlib

/-!
# La Matematica della Verità - Ettore Casari
Formalizzazione in Lean 4 tramite `mathlib` dei concetti fondamentali.
In Lean, il "discorso generale" sugli insiemi avviene parametrizzando
le definizioni su un Tipo Universo `V`. Le classi di Casari sono modellate come `Set V`.
-/

namespace Casari

section PartePrima_Classi

variable {V : Type*} 

/-! ### Capitolo 1: Classi -/

-- 1.3.1. Definizione: Uguaglianza fra classi
-- Casari: A ≡ B := ∀x(x ∈ A ↔ x ∈ B)
theorem def_1_3_1 (A B : Set V) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := 
  Set.ext_iff

-- 1.3.3. Definizione: Inclusione
-- Casari: A ⊆ B := ∀x(x ∈ A → x ∈ B)
theorem def_1_3_3 (A B : Set V) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := 
  Iff.rfl

-- 1.3.6. Teorema: Riflessività, Transitività e Antisimetria dell'inclusione
theorem thm_1_3_6_1 (A : Set V) : A ⊆ A := fun _ h => h
theorem thm_1_3_6_2 {A B C : Set V} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := fun _ h => h2 (h1 h)
theorem thm_1_3_6_3 {A B : Set V} (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := Set.ext fun _ => ⟨@h1 _, @h2 _⟩

-- 1.5.1. Definizione: Intersezione e Riunione
theorem def_1_5_1_1 (A B : Set V) : A ∩ B = {x | x ∈ A ∧ x ∈ B} := rfl
theorem def_1_5_1_2 (A B : Set V) : A ∪ B = {x | x ∈ A ∨ x ∈ B} := rfl

-- 1.5.4. Teorema: Proprietà dell'intersezione e della riunione
-- [1] Associatività,[2] Commutatività, [3] Idempotenza
theorem thm_1_5_4_1_1 (A B C : Set V) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := Set.inter_assoc A B C
theorem thm_1_5_4_1_2 (A B : Set V) : A ∩ B = B ∩ A := Set.inter_comm A B
theorem thm_1_5_4_1_3 (A : Set V) : A ∩ A = A := Set.inter_self A

theorem thm_1_5_4_2_1 (A B C : Set V) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := Set.union_assoc A B C
theorem thm_1_5_4_2_2 (A B : Set V) : A ∪ B = B ∪ A := Set.union_comm A B
theorem thm_1_5_4_2_3 (A : Set V) : A ∪ A = A := Set.union_self A

-- 1.7. Complemento
-- 1.7.3. Teorema: Leggi di De Morgan e doppia negazione
theorem thm_1_7_3_1 (A : Set V) : Aᶜᶜ = A := compl_compl A
theorem thm_1_7_3_4_1 (A B : Set V) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B
theorem thm_1_7_3_4_2 (A B : Set V) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := Set.compl_union A B

-- 1.8. Differenza simmetrica
-- In Mathlib questa operazione è definita universalmente sui reticoli booleani
-- (denotata con ∆ in alcuni testi, Casari usa +)
theorem def_1_8_1 (A B : Set V) : symmDiff A B = (A \ B) ∪ (B \ A) := rfl

/-! ### Capitolo 2: Relazioni -/

-- Le relazioni binarie per Casari sono classi di coppie ordinate.
-- In Lean, l'isomorfismo di Curry ci permette di modellarle nativamente come funzioni a valori in Prop.
def Rel (V W : Type*) := V → W → Prop

-- 2.5. Operazioni peirceane
-- 2.5.1. Definizione: Prodotto relativo (Composizione) e Converso
def peirce_comp {V W Z : Type*} (R : Rel V W) (S : Rel W Z) : Rel V Z :=
  fun x z => ∃ y, R x y ∧ S y z

def peirce_conv {V W : Type*} (R : Rel V W) : Rel W V :=
  fun y x => R x y

-- 2.5.3. Teorema: Associatività del prodotto peirceano
theorem thm_2_5_3_1 {V W Z U : Type*} (R : Rel V W) (S : Rel W Z) (T : Rel Z U) :
    peirce_comp (peirce_comp R S) T = peirce_comp R (peirce_comp S T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hR, hS⟩, hT⟩
    exact ⟨y, hR, z, hS, hT⟩
  · rintro ⟨y, hR, z, hS, hT⟩
    exact ⟨z, ⟨y, hR, hS⟩, hT⟩

-- 2.10. Proprietà delle relazioni (Riflessività, Simmetria, Transitività)
def is_reflexive (R : Rel V V) : Prop := ∀ x, R x x
def is_symmetric (R : Rel V V) : Prop := ∀ x y, R x y → R y x
def is_transitive (R : Rel V V) : Prop := ∀ x y z, R x y → R y z → R x z


/-! ### Capitolo 3: Funzioni -/

open Function

-- 3.5 Iniezioni, suriezioni, biiezioni
-- Casari definisce l'iniettività e suriettività via equazioni relazionali. 
-- In Lean, questo è gestito nativamente dal namespace `Function`.
theorem thm_3_5_2_inj {A B : Type*} (f : A → B) : 
    Injective f ↔ ∀ x y, f x = f y → x = y := Iff.rfl

theorem def_3_5_8_surj {A B : Type*} (f : A → B) : 
    Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl

theorem def_3_5_11_bij {A B : Type*} (f : A → B) : 
    Bijective f ↔ Injective f ∧ Surjective f := Iff.rfl

end PartePrima_Classi


section ParteSeconda_Strutture

/-! ### Capitolo 5: Gruppoidi -/

-- In Lean, il concetto di "Gruppoide" universale con una singola operazione binaria
-- definita in 5.1.1 è catturato dalla typeclass `Mul G` (oppure `Add G`). Per evitare
-- conflitti globali, introduciamo i tipi richiesti di volta in volta.

-- 5.2. Gruppoidi associativi (Semigruppi)
-- La condizione A. x ∘ (y ∘ z) = (x ∘ y) ∘ z è assunta dalla Typeclass `Semigroup`.
theorem thm_5_2_1 {G : Type*} [Semigroup G] (x y z : G) : (x * y) * z = x * (y * z) := mul_assoc x y z

-- 5.2.3. Definizione: Gruppoide commutativo (Semigruppo Abeliano)
theorem def_5_2_3 {G : Type*} [CommSemigroup G] (x y : G) : x * y = y * x := mul_comm x y

-- 5.4.6. Definizione: Monoide (Semigruppo unitario)
-- Unità sinistra e destra coincidono. Catturato dalla typeclass `Monoid`.
theorem def_5_4_6_ident {G : Type*} [Monoid G] (x : G) : x * 1 = x ∧ 1 * x = x := 
  ⟨mul_one x, one_mul x⟩

-- 5.6.2. Definizione: Gruppo
-- Un monoide invertibile a sinistra e a destra. Catturato da `Group`.
theorem def_5_6_2_inv {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 ∧ x⁻¹ * x = 1 := 
  ⟨mul_inv_cancel x, inv_mul_cancel x⟩


/-! ### Capitolo 6: Preordini -/

-- 6.1.1. Definizione: Preordine
-- Una relazione binaria riflessiva e transitiva. In Lean è modellato da `Preorder P`.
variable {P : Type*} [Preorder P]

theorem def_6_1_1_refl (x : P) : x ≤ x := le_refl x
theorem def_6_1_1_trans (x y z : P) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := le_trans h1 h2

-- 6.1.4. Definizione: Ordine (Parziale)
-- Un preordine antisimmetrico. In Lean è `PartialOrder O`.
variable {O : Type*} [PartialOrder O]
theorem def_6_1_4_antisymm (x y : O) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := le_antisymm h1 h2


/-! ### Capitolo 8: Reticoli -/

-- 8.1.1. Definizione: Un reticolo è un'algebra ⟨V, ⊓, ⊔⟩ che soddisfa L1, L2, L3.
-- Ovvero: idempotenza, commutatività e assorbimento. In Lean è `Lattice L`.
variable {L : Type*} [Lattice L]

-- Condizioni di commutatività
theorem reticolo_comm_inf (x y : L) : x ⊓ y = y ⊓ x := inf_comm x y
theorem reticolo_comm_sup (x y : L) : x ⊔ y = y ⊔ x := sup_comm x y

-- Leggi di assorbimento (L3)
theorem reticolo_abs_inf_sup (x y : L) : x ⊓ (x ⊔ y) = x := inf_sup_self
theorem reticolo_abs_sup_inf (x y : L) : x ⊔ (x ⊓ y) = x := sup_inf_self

-- 8.2.4. Definizione: Reticolo Distributivo
variable {D : Type*} [DistribLattice D]
theorem def_8_2_4_distrib (x y z : D) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := inf_sup_left x y z

-- 8.4. Algebre di Boole
-- Un reticolo distributivo e complementato. Lean: `BooleanAlgebra B`.
variable {B : Type*} [BooleanAlgebra B]

-- 8.4.1. Teorema B10.1 (Complemento)
theorem def_8_4_1_compl_inf (x y : B) : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := compl_inf
theorem def_8_4_1_compl_sup (x y : B) : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := compl_sup


/-! ### Capitolo 9: Spazi topologici -/

-- 9.2.1. Definizione: Uno spazio topologico è una famiglia moltiplicativa e 
-- completamente additiva di aperti.
-- Lean: `TopologicalSpace T` usa esattamente questa formulazione assiomatica.
variable {T : Type*}[TopologicalSpace T]

theorem top_univ_open : IsOpen (Set.univ : Set T) := isOpen_univ
theorem top_inter_open (A B : Set T) (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∩ B) := IsOpen.inter hA hB
theorem top_sUnion_open (F : Set (Set T)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := isOpen_sUnion hF

-- 9.4.1. Definizione: Funzione Continua
-- Inversa convergenza degli aperti (controsociativa per gli aperti).
variable {T' : Type*}[TopologicalSpace T']

theorem def_9_4_1_cont (f : T → T') : Continuous f ↔ ∀ A, IsOpen A → IsOpen (f ⁻¹' A) := continuous_def

-- 9.9.13 Spazio di Hausdorff (T2)
-- Teorema 9.9.14 (Proprietà di separazione)
variable[T2Space T]
theorem thm_9_9_14_t2 (x y : T) (h : x ≠ y) : 
    ∃ U V : Set T, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := 
  t2_separation h

end ParteSeconda_Strutture


section ParteTerza_Categorie

/-! ### Capitolo 10: Categorie -/

open CategoryTheory

-- 10.2. Categorie
-- Definite via operatori Hom, composizione e identità, con associatività
variable {C : Type*} [Category C]

-- Identità
#check 𝟙 -- Corrisponde all'Identità Categorica (CategoryStruct.id)
-- Composizione
#check (· ≫ ·) -- Corrisponde alla Composizione Categorica (CategoryStruct.comp)

-- Condizioni di identità e associatività assicurate assiomaticamente:
-- 10.2.1.2. Associatività e Elemento neutro
#check Category.id_comp
#check Category.comp_id
#check Category.assoc

/-! ### Capitolo 11: Categorie di categorie e di funtori -/

-- 11.2.1 Funtori (Covarianti)
-- Un funtore F : C ⟶ D mappa oggetti in oggetti e frecce in frecce preservando identità e composizione.
variable {D : Type*} [Category D]
variable (F : C ⥤ D) -- `F` è un'entità di tipo `Functor C D`

-- Conservazione dell'identità
#check F.map_id 
-- Conservazione della composizione
#check F.map_comp

-- 11.6. Trasformazioni naturali
-- Famiglia indicizzata di frecce che rende commutativi i quadrati indotti dalle frecce della categoria dominio.
variable (G : C ⥤ D)
variable (α : F ⟶ G) -- `NatTrans F G`

-- Condizione di naturalità (commutatività del diagramma)
#check α.naturality

-- 11.9 Lemma di Yoneda
-- Asserisce l'isomorfismo naturale fra le trasformazioni naturali Hom(A, -) ⟶ F e gli elementi di F(A).
-- In Mathlib questa maestosa architettura è già fornita dal Funtore di Yoneda: `CategoryTheory.yoneda`
#check yoneda
#check yonedaEquiv

end ParteTerza_Categorie
end Casari