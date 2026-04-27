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

def peirce_residual_right {V W Z : Type*} (R : Rel V W) (S : Rel V Z) : Rel W Z :=
  fun y z => ∀ x, R x y → S x z

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
variable {P : Type*}[Preorder P]

theorem def_6_1_1_refl (x : P) : x ≤ x := le_refl x
theorem def_6_1_1_trans (x y z : P) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := le_trans h1 h2

-- 6.1.4. Definizione: Ordine (Parziale)
-- Un preordine antisimmetrico. In Lean è `PartialOrder O`.
variable {O : Type*}[PartialOrder O]
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
variable {D : Type*}[Category D]
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

open Function
open Set
open Filter
open TopologicalSpace
open CategoryTheory
open CategoryTheory.Limits

namespace Casari

variable {V : Type*}

/-! ### Capitolo 4: Famiglie su un insieme -/

-- 4.6. Filtri e Ideali di insiemi
-- Casari definisce un filtro su V come una famiglia non vuota chiusa per soprainsiemi e intersezione finita.
-- In Lean, questo è esattamente il tipo `Filter V`.
theorem def_4_6_1_filtro_F1 (F : Filter V) {A B : Set V} (hA : A ∈ F) (hSub : A ⊆ B) : B ∈ F :=
  Filter.mem_of_superset hA hSub

theorem def_4_6_1_filtro_F2 (F : Filter V) {A B : Set V} (hA : A ∈ F) (hB : B ∈ F) : A ∩ B ∈ F :=
  Filter.inter_mem hA hB

-- In modo duale, un ideale (di insiemi) è chiuso per sottoinsiemi e riunione.
-- In Mathlib gli ideali sono definiti universalmente sugli ordini parziali. 
-- Un ideale di insiemi è un `Order.Ideal (Set V)`.
theorem def_4_6_5_ideale_I1 (I : Order.Ideal (Set V)) {A B : Set V} (hA : A ∈ I) (hB : B ∈ I) : A ∪ B ∈ I :=
  I.sup_mem hA hB

theorem def_4_6_5_ideale_I2 (I : Order.Ideal (Set V)) {A B : Set V} (hA : A ∈ I) (hSub : B ⊆ A) : B ∈ I :=
  I.lower hSub hA


/-! ### Capitolo 6: Preordini e Ordini Completi -/

variable {P : Type*} [PartialOrder P]

-- 6.4. Confini, minimi, massimi, infimi e supremi
-- Un maggiorante (confine superiore) per Casari è un elemento x tale che ∀ y ∈ A, y ≤ x.
theorem def_6_4_1_maggiorante (A : Set P) (x : P) : 
    x ∈ upperBounds A ↔ ∀ y ∈ A, y ≤ x := Iff.rfl

theorem def_6_4_1_minorante (A : Set P) (x : P) : 
    x ∈ lowerBounds A ↔ ∀ y ∈ A, x ≤ y := Iff.rfl

-- 6.4.15 Definizione di Supremo (LUB) e Infimo (GLB)
-- In Lean, la corrispondenza è la classe predicativa `IsLUB` e `IsGLB`.
theorem def_6_4_15_supremo (A : Set P) (x : P) : 
    IsLUB A x ↔ (x ∈ upperBounds A ∧ ∀ y ∈ upperBounds A, x ≤ y) := Iff.rfl

-- 6.7. Ordini completi
-- Un ordine che ammette estremo superiore e inferiore per ogni sottoinsieme.
-- In Lean questo è formalizzato dalla typeclass `CompleteLattice`.
variable {C : Type*} [CompleteLattice C]

theorem thm_6_7_4_completo (A : Set C) : ∃ x y : C, IsLUB A x ∧ IsGLB A y :=
  ⟨sSup A, sInf A, isLUB_sSup A, isGLB_sInf A⟩


/-! ### Capitolo 7: Strutture ordinate -/

-- 7.4. Connessioni di Galois
-- Una connessione di Galois fra due insiemi ordinati (covariante).
variable {A B : Type*} [PartialOrder A][PartialOrder B]
variable (l : A → B) (u : B → A)

theorem def_7_4_2_connessione_di_galois (gc : GaloisConnection l u) (a : A) (b : B) : 
    l a ≤ b ↔ a ≤ u b := gc a b

-- 7.6. Gruppoidi residuati e coresiduati
-- Base della "Logica Lineare" e di altre logiche sottostrutturali. 
-- La residuazione stabilisce l'esistenza di un'operazione ⇨ (implicazione/residuo).


/-! ### Capitolo 8: Reticoli (Raffinamenti) -/

-- 8.6.17. Algebre di Heyting
-- I reticoli pseudocomplementati limitati in cui l'operazione di residuazione 
-- funge da implicazione intuizionista prendono il nome di Algebre di Heyting.
variable {H : Type*}[HeytingAlgebra H]

-- Legge fondamentale di Brouwer / Residuo intuizionista
theorem def_8_6_17_heyting (a b c : H) : 
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c := Iff.symm le_himp_iff

-- In un'algebra di Heyting, il Terzo Escluso in generale non vale: 
-- Non è detto che `a ⊔ aᶜ = ⊤`. Tuttavia `a ≤ aᶜᶜ` vale sempre.
theorem thm_intuizionista_doppia_neg (a : H) : a ≤ aᶜᶜ := le_compl_compl


/-! ### Capitolo 9: Spazi topologici -/

variable {X : Type u} [TopologicalSpace X]

-- 9.7. Operazioni di chiusura e di interno
-- Casari le descrive tramite convergenze e assiomi di Kuratowski.
theorem thm_9_7_4_int (A : Set X) : interior A ⊆ A := interior_subset
theorem thm_9_7_4_clos (A : Set X) : A ⊆ closure A := subset_closure

-- Dualità topologica tra interno e chiusura
theorem thm_9_7_4_dualita (A : Set X) : interior A = (closure Aᶜ)ᶜ := 
  interior_eq_compl_closure_compl

-- 9.11. Proprietà di compattezza
-- Teorema 9.11.2: Un sottoinsieme è compatto sse da ogni sua copertura aperta si può estrarre un sottoricoprimento finito.
-- In Lean questa assiomatizzazione usa nativamente le famiglie di aperti.
theorem thm_9_11_2_borel_lebesgue (A : Set X) : 
    IsCompact A ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i → ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i := 
  isCompact_iff_finite_subcover

-- 9.12. Spazi di Boole
-- Uno spazio si dice di Boole se è compatto, di Hausdorff e totalmente sconnesso.
-- È l'analogo topologico (spazio di Stone) delle algebre di Boole.
variable [CompactSpace X] [T2Space X][TotallyDisconnectedSpace X]

-- Ogni spazio di Boole (o Spazio di Stone) è zero-dimensionale (ammette una base di "clopen").
-- Questo fatto in `mathlib` è incapsulato via l'isomorfismo per gli spazi profiniti.


/-! ### Capitolo 10 & 11: Categorie e Categorie di Funtori -/

variable {Cat : Type u} [Category.{v} Cat]

-- 10.6 Prodotti Categorici
variable [HasBinaryProducts Cat]

-- Il limite di uno span senza frecce, o equivalentemente il prodotto cartesiano categorico,
-- è interamente incapsulato nel limite binario in Mathlib.
#check Limits.prod.fst  -- Proiezione sul primo fattore (π₁)
#check Limits.prod.snd  -- Proiezione sul secondo fattore (π₂)
#check Limits.prod.lift -- Proprietà universale del prodotto

-- 10.8 Equalizzatori
variable[HasEqualizers Cat]
#check Limits.equalizer.ι -- La freccia che equalizza il diagramma

-- 11.10. Aggiunzione (Adjunctions)
-- I funtori aggiunti rappresentano il cuore categoriale delle connessioni di Galois.
variable {C_cat D_cat : Type u} [Category.{v} C_cat][Category.{v} D_cat]
variable (L : C_cat ⥤ D_cat) (R : D_cat ⥤ C_cat)

-- La sintassi `L ⊣ R` descrive che `L` è aggiunto sinistro di `R`.
#check L ⊣ R
#check Adjunction.homEquiv -- L'isomorfismo naturale Hom(L(X), Y) ≅ Hom(X, R(Y))


/-! ### Appendice B: Cenni di logica algebrica (Algebre di Lindenbaum-Tarski) -/

-- Casari spiega come l'insieme delle formule F di un linguaggio, quozientato 
-- rispetto alla relazione di provata equivalenza logica (T ⊢ α ↔ β), dia luogo a un'algebra.

-- Modelliamo il concetto astratto di questa "Algebra delle formule".
-- Supponiamo che `Form` sia il nostro linguaggio chiuso per connettivi booleani.
-- Se il sistema assiomatico gode della logica classica, l'algebra di Lindenbaum 
-- diventa un'Algebra di Boole. In Lean non abbiamo bisogno di costruire a mano 
-- il setoide e il quoziente per goderne le proprietà semantiche: la trattazione è
-- intrinsecamente sussunta dall'astrazione di `BooleanAlgebra`.

variable {Form : Type*} [BooleanAlgebra Form]

-- L'equivalenza logica α ≈ β corrisponde all'uguaglianza nel quoziente α = β.
-- La deduzione (implicazione logica) α ⊢ β corrisponde all'ordine parziale α ≤ β.
-- Dimostriamo il Teorema di Deduzione algebrico (l'equivalenza con la Tautologia):
-- α ⊢ β se e solo se (α ⇨ β) è una tautologia (il massimo del reticolo, `⊤`).

theorem B_3_lindenbaum_tarski_implicazione (α β : Form) : 
    α ≤ β ↔ α ⇨ β = ⊤ := 
  himp_eq_top_iff.symm

-- Teorema di non-contraddittorietà (Consistenza):
-- Una teoria è consistente sse il suo elemento minimo ⊥ (falso) non è equivalente al massimo ⊤ (vero).
theorem B_3_consistenza[Nontrivial Form] : 
    (⊥ : Form) ≠ ⊤ := bot_ne_top

end Casari