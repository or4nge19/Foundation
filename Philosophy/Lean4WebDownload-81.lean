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

-- Usiamo un simbolo simile a quello di Casari ma non conflittuale con Mathlib (Triple bar)
local infix:50 " ≣ " => Eq

-- 1.3.1. Definizione: Uguaglianza fra classi
-- Casari: A ≡ B := ∀x(x ∈ A ↔ x ∈ B)
theorem def_1_3_1 (A B : Set V) : A ≣ B ↔ ∀ x, x ∈ A ↔ x ∈ B := 
  Set.ext_iff

-- 1.3.3. Definizione: Inclusione
-- Casari: A ⊆ B := ∀x(x ∈ A → x ∈ B)
theorem def_1_3_3 (A B : Set V) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := 
  Iff.rfl

-- 1.3.6. Teorema: Riflessività, Transitività e Antisimetria dell'inclusione
theorem thm_1_3_6_1 (A : Set V) : A ⊆ A := fun _ h => h
theorem thm_1_3_6_2 {A B C : Set V} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := fun _ h => h2 (h1 h)
theorem thm_1_3_6_3 {A B : Set V} (h1 : A ⊆ B) (h2 : B ⊆ A) : A ≣ B := Set.ext fun _ => ⟨@h1 _, @h2 _⟩

-- 1.5.1. Definizione: Intersezione e Riunione
theorem def_1_5_1_1 (A B : Set V) : A ∩ B ≣ {x | x ∈ A ∧ x ∈ B} := rfl
theorem def_1_5_1_2 (A B : Set V) : A ∪ B ≣ {x | x ∈ A ∨ x ∈ B} := rfl

-- 1.5.4. Teorema: Proprietà dell'intersezione e della riunione
theorem thm_1_5_4_1_1 (A B C : Set V) : (A ∩ B) ∩ C ≣ A ∩ (B ∩ C) := Set.inter_assoc A B C
theorem thm_1_5_4_1_2 (A B : Set V) : A ∩ B ≣ B ∩ A := Set.inter_comm A B
theorem thm_1_5_4_1_3 (A : Set V) : A ∩ A ≣ A := Set.inter_self A

theorem thm_1_5_4_2_1 (A B C : Set V) : (A ∪ B) ∪ C ≣ A ∪ (B ∪ C) := Set.union_assoc A B C
theorem thm_1_5_4_2_2 (A B : Set V) : A ∪ B ≣ B ∪ A := Set.union_comm A B
theorem thm_1_5_4_2_3 (A : Set V) : A ∪ A ≣ A := Set.union_self A

-- 1.7. Complemento
theorem thm_1_7_3_1 (A : Set V) : Aᶜᶜ ≣ A := compl_compl A
theorem thm_1_7_3_4_1 (A B : Set V) : (A ∩ B)ᶜ ≣ Aᶜ ∪ Bᶜ := Set.compl_inter A B
theorem thm_1_7_3_4_2 (A B : Set V) : (A ∪ B)ᶜ ≣ Aᶜ ∩ Bᶜ := Set.compl_union A B

-- 1.8. Differenza simmetrica
theorem def_1_8_1 (A B : Set V) : symmDiff A B ≣ (A \ B) ∪ (B \ A) := rfl

/-! ### Capitolo 2: Relazioni -/

-- Abbrev rende trasparente il tipo per LE (inclusione logica point-wise)
abbrev Rel (V W : Type*) := V → W → Prop

-- 2.5. Operazioni peirceane
def peirce_comp {V W Z : Type*} (R : Rel V W) (S : Rel W Z) : Rel V Z :=
  fun x z => ∃ y, R x y ∧ S y z

def peirce_conv {V W : Type*} (R : Rel V W) : Rel W V :=
  fun y x => R x y

-- Notazione locale in stile Casari per le relazioni
local infixl:80 " ⚬ " => peirce_comp
local postfix:max "˘" => peirce_conv

-- 2.5.3. Teorema: Associatività del prodotto peirceano
theorem thm_2_5_3_1 {V W Z U : Type*} (R : Rel V W) (S : Rel W Z) (T : Rel Z U) :
    (R ⚬ S) ⚬ T ≣ R ⚬ (S ⚬ T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hR, hS⟩, hT⟩
    exact ⟨y, hR, z, hS, hT⟩
  · rintro ⟨y, hR, z, hS, hT⟩
    exact ⟨z, ⟨y, hR, hS⟩, hT⟩

-- 2.6. Residuazioni e coresiduazioni
def peirce_residual_right {V W Z : Type*} (R : Rel V W) (S : Rel V Z) : Rel W Z :=
  fun y z => ∀ x, R x y → S x z

local infixr:65 " ▹ " => peirce_residual_right

-- 2.6.2 Teorema: Legge di Aggiunzione fondamentale
theorem thm_2_6_2_adjunction {V W Z : Type*} (R : Rel V W) (S : Rel W Z) (T : Rel V Z) :
    (R ⚬ S) ≤ T ↔ S ≤ (R ▹ T) := by
  constructor
  · intro h y z hS x hR
    exact h x z ⟨y, hR, hS⟩
  · intro h x z ⟨y, hR, hS⟩
    exact h y z hS x hR

-- 2.10. Proprietà delle relazioni
def is_reflexive (R : Rel V V) : Prop := ∀ x, R x x
def is_symmetric (R : Rel V V) : Prop := ∀ x y, R x y → R y x
def is_transitive (R : Rel V V) : Prop := ∀ x y z, R x y → R y z → R x z


/-! ### Capitolo 3: Funzioni -/

open Function

theorem thm_3_5_2_inj {A B : Type*} (f : A → B) : 
    Injective f ↔ ∀ x y, f x = f y → x = y := Iff.rfl

theorem def_3_5_8_surj {A B : Type*} (f : A → B) : 
    Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl

theorem def_3_5_11_bij {A B : Type*} (f : A → B) : 
    Bijective f ↔ Injective f ∧ Surjective f := Iff.rfl

end PartePrima_Classi


section ParteSeconda_Strutture

/-! ### Capitolo 5: Gruppoidi -/

theorem thm_5_2_1 {G : Type*} [Semigroup G] (x y z : G) : (x * y) * z = x * (y * z) := mul_assoc x y z

theorem def_5_2_3 {G : Type*} [CommSemigroup G] (x y : G) : x * y = y * x := mul_comm x y

-- 5.4.6 Monoide (Semigruppo unitario)
theorem def_5_4_6_ident {G : Type*} [Monoid G] (x : G) : x * 1 = x ∧ 1 * x = x := 
  ⟨mul_one x, one_mul x⟩

theorem def_5_6_2_inv {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 ∧ x⁻¹ * x = 1 := 
  ⟨mul_inv_cancel x, inv_mul_cancel x⟩


/-! ### Capitolo 6: Preordini -/

variable {P : Type*} [Preorder P]

theorem def_6_1_1_refl (x : P) : x ≤ x := le_refl x
theorem def_6_1_1_trans (x y z : P) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := le_trans h1 h2

variable {O : Type*} [PartialOrder O]
theorem def_6_1_4_antisymm (x y : O) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := le_antisymm h1 h2


/-! ### Capitolo 8: Reticoli -/

variable {L : Type*} [Lattice L]

theorem reticolo_comm_inf (x y : L) : x ⊓ y = y ⊓ x := inf_comm x y
theorem reticolo_comm_sup (x y : L) : x ⊔ y = y ⊔ x := sup_comm x y
theorem reticolo_abs_inf_sup (x y : L) : x ⊓ (x ⊔ y) = x := inf_sup_self
theorem reticolo_abs_sup_inf (x y : L) : x ⊔ (x ⊓ y) = x := sup_inf_self

variable {D : Type*} [DistribLattice D]
theorem def_8_2_4_distrib (x y z : D) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := inf_sup_left x y z

variable {B : Type*} [BooleanAlgebra B]
theorem def_8_4_1_compl_inf (x y : B) : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := compl_inf
theorem def_8_4_1_compl_sup (x y : B) : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := compl_sup


/-! ### Capitolo 9: Spazi topologici -/

variable {T : Type*} [TopologicalSpace T]

theorem top_univ_open : IsOpen (Set.univ : Set T) := isOpen_univ
theorem top_inter_open (A B : Set T) (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∩ B) := IsOpen.inter hA hB
theorem top_sUnion_open (F : Set (Set T)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := isOpen_sUnion hF

variable {T' : Type*} [TopologicalSpace T']
theorem def_9_4_1_cont (f : T → T') : Continuous f ↔ ∀ A, IsOpen A → IsOpen (f ⁻¹' A) := continuous_def

variable [T2Space T]
theorem thm_9_9_14_t2 (x y : T) (h : x ≠ y) : 
    ∃ U V : Set T, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := 
  t2_separation h

end ParteSeconda_Strutture


section ParteTerza_Categorie

open CategoryTheory

variable {C : Type*} [Category C]

#check 𝟙 
#check (· ≫ ·) 

#check Category.id_comp
#check Category.comp_id
#check Category.assoc


/-! ### Capitolo 11: Categorie di categorie e di funtori -/

variable {D : Type*} [Category D]
variable (F : C ⥤ D)

#check F.map_id 
#check F.map_comp

variable (G : C ⥤ D)
variable (α : F ⟶ G)

#check α.naturality

#check yoneda
#check yonedaEquiv

end ParteTerza_Categorie
end Casari


open Function Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Casari

variable {V : Type*}

/-! ### Capitolo 4: Famiglie su un insieme -/

theorem def_4_6_1_filtro_F1 (F : Filter V) {A B : Set V} (hA : A ∈ F) (hSub : A ⊆ B) : B ∈ F :=
  Filter.mem_of_superset hA hSub

theorem def_4_6_1_filtro_F2 (F : Filter V) {A B : Set V} (hA : A ∈ F) (hB : B ∈ F) : A ∩ B ∈ F :=
  Filter.inter_mem hA hB

theorem def_4_6_5_ideale_I1 (I : Order.Ideal (Set V)) {A B : Set V} (hA : A ∈ I) (hB : B ∈ I) : A ∪ B ∈ I :=
  I.sup_mem hA hB

theorem def_4_6_5_ideale_I2 (I : Order.Ideal (Set V)) {A B : Set V} (hA : A ∈ I) (hSub : B ⊆ A) : B ∈ I :=
  I.lower hSub hA


/-! ### Capitolo 6: Preordini e Ordini Completi -/

variable {P : Type*} [PartialOrder P]

theorem def_6_4_1_maggiorante (A : Set P) (x : P) : 
    x ∈ upperBounds A ↔ ∀ y ∈ A, y ≤ x := Iff.rfl

theorem def_6_4_1_minorante (A : Set P) (x : P) : 
    x ∈ lowerBounds A ↔ ∀ y ∈ A, x ≤ y := Iff.rfl

theorem def_6_4_15_supremo (A : Set P) (x : P) : 
    IsLUB A x ↔ (x ∈ upperBounds A ∧ ∀ y ∈ upperBounds A, x ≤ y) := Iff.rfl

variable {C : Type*} [CompleteLattice C]
theorem thm_6_7_4_completo (A : Set C) : ∃ x y : C, IsLUB A x ∧ IsGLB A y :=
  ⟨sSup A, sInf A, isLUB_sSup A, isGLB_sInf A⟩


/-! ### Capitolo 7: Strutture ordinate -/

variable {A B : Type*} [PartialOrder A] [PartialOrder B]
variable (l : A → B) (u : B → A)

-- 7.4.2. Connessione di Galois
theorem def_7_4_2_connessione_di_galois (gc : GaloisConnection l u) (a : A) (b : B) : 
    l a ≤ b ↔ a ≤ u b := gc a b

-- 7.4.3. Esempio fondamentale: Immagine e controimmagine formano una connessione di Galois
theorem ex_7_4_3_image_preimage_gc {X Y : Type*} (f : X → Y) :
    GaloisConnection (image f) (preimage f) := 
  fun _ _ => image_subset_iff


/-! ### Capitolo 8: Reticoli (Raffinamenti) -/

variable {H : Type*} [HeytingAlgebra H]

-- 8.6.17. Algebre di Heyting (Legge fondamentale di Brouwer)
theorem def_8_6_17_heyting (a b c : H) : 
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c := Iff.symm le_himp_iff

theorem thm_intuizionista_doppia_neg (a : H) : a ≤ aᶜᶜ := le_compl_compl


/-! ### Capitolo 9: Spazi topologici -/

variable {X : Type u} [TopologicalSpace X]

-- 9.7. Operazioni di chiusura e di interno
theorem thm_9_7_4_int (A : Set X) : interior A ⊆ A := interior_subset
theorem thm_9_7_4_clos (A : Set X) : A ⊆ closure A := subset_closure

theorem thm_9_7_4_dualita (A : Set X) : interior A = (closure Aᶜ)ᶜ := 
  interior_eq_compl_closure_compl

-- 9.11. Proprietà di compattezza (Borel-Lebesgue)
theorem thm_9_11_2_borel_lebesgue (A : Set X) : 
    IsCompact A ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i → ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i := 
  isCompact_iff_finite_subcover

-- 9.12. Spazi di Boole (o Spazi di Stone)
variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

-- 9.12.1. Insiemi Clopen (Aperti-Chiusi)
theorem def_9_12_1_clopen (A : Set X) : 
    IsClopen A ↔ IsOpen A ∧ IsClosed A :=
  ⟨fun h => ⟨h.isOpen, h.isClosed⟩, fun h => ⟨h.1, h.2⟩⟩

-- 9.12.4. Teorema: Ogni spazio di Boole possiede una base di aperti-chiusi (clopen).
theorem thm_9_12_4_basis : 
    IsTopologicalBasis {U : Set X | IsClopen U} := 
  isTopologicalBasis_clopen


/-! ### Capitolo 10 & 11: Categorie e Categorie di Funtori -/

variable {Cat : Type u} [Category.{v} Cat]

variable [HasBinaryProducts Cat]
#check Limits.prod.fst 
#check Limits.prod.snd 
#check Limits.prod.lift 

variable [HasEqualizers Cat]
#check Limits.equalizer.ι 

variable {C_cat D_cat : Type u} [Category.{v} C_cat] [Category.{v} D_cat]
variable (L : C_cat ⥤ D_cat) (R : D_cat ⥤ C_cat)

#check L ⊣ R
#check Adjunction.homEquiv 


/-! ### Appendice B: Cenni di logica algebrica (Algebre di Lindenbaum-Tarski) -/

variable {Form : Type*} [BooleanAlgebra Form]

theorem B_3_lindenbaum_tarski_implicazione (α β : Form) : 
    α ≤ β ↔ α ⇨ β = ⊤ := 
  himp_eq_top_iff.symm

theorem B_3_consistenza [Nontrivial Form] : 
    (⊥ : Form) ≠ ⊤ := bot_ne_top

end Casari