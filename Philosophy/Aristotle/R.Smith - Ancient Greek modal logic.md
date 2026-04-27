# Chapter 29
# ANCIENT GREEK MODAL LOGIC

Robin Smith

Formal logic began in classical Greece. Aristotle’s *Prior Analytics* contains a fully developed theory of logical inference, with mathematical proofs for the validity of forms of inference and some metalogical results. While no earlier logical work has survived, Aristotle’s contemporaries and immediate precursors appear also to have studied logical inference, and we can trace a separate line of development for logical theory from the “Megarians” that is clearly flourishing a generation later with Diodorus Cronus and the “Dialectical School.” From this descended the logic of the Stoics, among whom Chrysippus became the most celebrated logician of the Hellenistic period. Unfortunately, our knowledge of this alternative tradition is very fragmentary.

Modal logic, that is, the study of inferences in which necessity, possibility, and impossibility play a role, was pursued in both these traditions. The theory of inference in Aristotle’s *Prior Analytics* I.1–7 (usually called the syllogistic) has been shown by modern studies to be a masterful development. However, his modal extension of this in *Prior Analytics* I.8–22 is far more problematic and has often been seen as incoherent. By contrast, we know far less about the study of modal logic in the alternative tradition represented by the Stoics, since very little has survived apart from indirect accounts. In what follows, I first discuss the treatment of necessity and possibility in the broad historical context of ancient Greek logic and philosophy, and then turn to the details of Aristotle’s system.

First, however, there is an important point of perspective. Modern formal logic takes the bearers of truth and falsehood to be propositions that are fully determinate. Utterances of declarative sentences express propositions, but which proposition a sentence expresses may vary with time and other contexts of utterance: “It’s raining here” uttered on January 1, 2000, in Chicago expresses a different proposition from that same sentence uttered in Cairo on July 1, 1900. In either case, the proposition expressed is either timelessly true or timelessly false. Ancient Greek logicians instead took propositions themselves to change their truth-value with the passage of time. Thus, the sentence “It’s raining in Chicago” expresses the same meaning uttered yesterday, today, and tomorrow, but its truth-value changes with the weather. This has consequences for understanding modally qualified propositions. The standard procedure for modal semantics in modern logic is to appeal to possible worlds (alternative ways things might have been). By contrast, Greek logicians tended to associate necessity with omnitemporality, so that a proposition is

331

***

Robin Smith

necessarily true if it is *always* true. For the Greeks, then, necessity is closely connected with unchangeability and possibility with changeability.

This takes on greater importance against the background of early Greek thought, where the distinction between what is necessary and what is possible was often linked with a metaphysical distinction, that between what is changeable and what is not. Parmenides (active in the early fifth century BCE) argued that since it is a contradiction to say that what is also is not, change cannot be real: if there were change, then what is not would have to be, which (on his view) is contradictory. Similarly, there cannot be a multiplicity of things, since that would require that there is something which is not some other thing, and thus something which both is and is not. However we interpret Parmenides’ arguments, they had an enormous impact on subsequent Greek philosophy. We find explicit responses to them in Anaxagoras, Democritus, Plato, and Aristotle. Plato instead developed a metaphysics involving two distinct realms, the realm of being (which is necessarily as it is, unchanging with time) and the realm of becoming, where we find that which “both is and is not.” Aristotle also tells us that a somewhat obscure group of philosophers, the Megarians, held that only what is actual is possible. If you are now sitting, then it is not possible that you are now standing, since it would be a contradiction to say that you are now sitting and now not sitting. If you attempt to refute this by standing up and thus showing that you can stand, the Megarians reply, that only shows that you can stand *now*, not that you could have stood *then*, when you were seated (see Aristotle, *Metaphysics* Θ.3).

### The necessity of the past and Diodorus’ “master” argument

This Megarian position can be given a sharper focus if we combine it with the principle that whatever has been true in the past is now necessarily true: if it is true that it rained yesterday in Chicago, then it is now necessarily true that it rained yesterday in Chicago. The unchangeability of the past is close to proverbial in ancient Greek thought:

For of this alone even a god is deprived,
To make undone those things that have been done.
(Agathon, quoted by Aristotle, *EN* 1139b10–11)

In *On Interpretation 9*, Aristotle criticizes an argument for the necessity of everything that happens resting on this principle and the principle of bivalence. Consider the proposition “There will be a sea-battle tomorrow,” interpreted as temporally definite, e.g. “There will be a sea-battle tomorrow, January 1, 2000.” Suppose, in addition, that every declarative sentence is, when uttered, necessarily either true or false. Therefore, this proposition, when uttered on December 31, 1999, was necessarily either true or false. However, if it was true when uttered, then since the past is now unchangeable, it is now necessarily true that it was true, and hence now necessary that there will be a sea-battle tomorrow. Moreover, whether or not the sentence in question was actually uttered on the day in question, all that matters is whether things were such as to make it true. If they were, then it is now necessarily true that they were, and hence now necessary that there will be a sea-battle tomorrow.

Aristotle thinks the conclusion of this argument is unacceptable, since it implies that there is no choice and that deliberation is pointless. However, though it is clear that he wants to reject it, it is far less clear just how he proposes to do so: an enormous literature has arisen on its interpretation. His remarks are contained in an extended discussion of what he calls “contradictions”

332

***

*Ancient Greek modal logic*

(*antitheseis*), i.e., pairs of sentences one of which affirms of its subject exactly what the other denies of that subject. While he holds that in general the members of any such contradiction must be one true and the other false, he argues that this may fail to hold for contradictions consisting of future contingent statements such as “There will be a sea-battle tomorrow” and “There will not be a sea-battle tomorrow.” While this much is obvious, there has been a long-standing controversy about exactly how he proposed to avoid it and about whether his view is coherent (among the vast literature on the subject, see Anscombe 1956; Hintikka 1964; Frede 1970; Whitaker 1996).

Aristotle does not name those who advanced the argument he is attacking, but, as noted earlier, in *Metaphysics* Θ 3 he attributes a shorter argument with the same purpose to “Megarians.” The association with the Megarians is significant, since a more fully developed version was advanced by Diodorus Cronus (died ca. 284 CE) who was probably influenced by Megarian logic, if not himself a member of the Megarian School (see Sedley 1977, 2018; Döring 1989; Ebert 2008). This argument, which Diodorus called the “Master” argument (*kurieuôn logos*), argued that these three propositions are an inconsistent triad:

(1) What is past is necessary.
(2) The impossible does not follow (from) the possible.
(3) There is something possible which neither is nor will be true.

Diodorus’ own response to the “Master” was to reject (3), leading to his definitions of the possible as “that which either is or will be true” and the necessary as “that which is true and never will be false.”

The Stoic school that arose in the latter half of the third century BCE took its logic largely from Diodorus and others of the Dialectical School, and developing a response to the “Master” became a major concern of Stoic logicians, though we know relatively little of the details. We do have at least a sketch of the response of Chrysippus (ca. 280–ca. 207 BCE), regarded in antiquity as the greatest Stoic logician. He accepted the mutual incompatibility of its three propositions but argued that the one to be rejected is “The impossible does not follow from the possible” by appealing to Stoic propositional semantics. He considered these propositions:

(1) If Dion is dead, then he [indicating Dion] is dead.
(2) Dion has died.
(3) He [indicating Dion] has died.

Using the criterion that a conditional proposition is true if and only if its antecedent is incompatible with the denial of its consequent, proposition (1) is true. Therefore, (3) does follow from (2). Moreover, since Dion is not immortal, (2) is possible. However, Chrysippus held that a proposition containing an indexical term (“he” in this case) “perishes” (ceases to exist) when the object ostended ceases to exist. Consequently, when Dion has died, (3) does not exist, and since it is therefore false at all times (i.e. whenever it exists), it is impossible. We therefore have something impossible that follows from something possible. Unfortunately, since our knowledge of Chrysippus’ argument relies on summaries by (sometimes hostile) others, we cannot say with confidence what further use he made of it. Since the Stoics were determinists, he may have been offering a response to the complaint that determinism makes everything necessary by displaying something that is possible but neither is nor will be true.

333

***

Robin Smith

### Aristotle’s modal logic

Aristotle’s modal logic is an extension of his basic logical system (the syllogistic), and so an account of it must begin with that basic system as presented in *Prior Analytics* I.1–7. The syllogistic is a theory of the inferential relationships among four types of categorical sentence:

Universal affirmative: Every human is two-footed
Particular affirmative: Some human is two-footed
Universal negative: No human is two-footed
Particular negative: Some human is not two-footed / Not every human is two-footed

Aristotle adopts a somewhat artificial way of expressing these categorical sentences, as they are usually called: “Every/Some/No A is B” becomes “B is predicated of every/some/no A” (this language is not at all ordinary Greek). For convenience, I abbreviate these as follows:

AaB: A is predicated of every/all B
AeB: A is predicated of no B
AiB: A is predicated of some B
AoB: A is not predicated of some B / A is not predicated of every B

He then investigates all possible combinations of pairs of premises having one term in common to see which “syllogize,” that is, entail as conclusion a categorical sentence using the other two terms in the premises. He first argues that four forms are valid on the basis of their semantics:

AaB, BaC |- AaC (traditionally called *Barbara* since the 13th century)
AeB, BaC |- AeC (*Celarent*)
AaB, BiC |- AiC (*Darii*)
AeB, BiC |- AoC (*Ferio*)

He characterizes these as “complete” or “perfect” (*teleios*), which for him appears to mean that their validity is evident from the meanings of the categorical sentences alone without requiring additional deductive steps. To prove the validity of further forms, he argues that certain conversion inferences hold (*An. Pr.* I.2):

AeB |- BeA
AiB |- BiA
AaB |- BiA

With these conversion rules plus a form of indirect proof (“proof through the impossible”), Aristotle then gives proofs for the validity of a further ten forms of argument, a type of natural deduction (see Corcoran 1974):

AaB, AeC |- BeC (*Camestres*)
AeB, AaC |- BeC (*Cesare*)
AeB, AiC |- BoC (*Festino*)
AaB, AoC |- BoC (*Baroco*)
AaC, BaC |- AiB (*Darapti*)
AeC, BaC |- AoB (*Felapton*)
AiC, BaC |- AiB (*Disamis*)

334

***

*Ancient Greek modal logic*

AaC, BiC |- AiB (*Datisi*)
AoC, BaC |- AoB (*Bocardo*)
AeC, BiC |- AoB (*Ferison*)

Aristotle also shows that combinations of premise forms other than these “do not syllogize” by offering countermodels: two triplets of terms such that, when substituted for the terms in the premise pair in question, they satisfy the premises but yield respectively a true putative universal affirmative and a true universal negative “conclusion.” Modern studies have shown that the resulting system is logically complete (Corcoran 1972). In addition to these methods, Aristotle sometimes notes that alternative proofs are possible using what he calls *ekthesis*, relying on these further rules:

AiB |- for some C, AaC and BaC
AoB |- for some C, AeC and BaC

While his system is complete without proofs through *ekthesis*, they are indispensable in the modal syllogistic.

I have described this theory as applying to a certain class of propositions, but Aristotle himself treats it as the theory of inference *tout court*, since he also believes, and believes he can show, that all valid inferences can be “reduced” to the “arguments in the figures,” as he calls his system (*An. Pr.* I 30).

### The modal syllogistic

The modal syllogistic is an expansion of this system that adds two additional forms of predication: “necessarily belongs” and “possibly belongs.” Aristotle considers what happens when “belongs” is replaced by “belongs necessarily” or “belongs possibly” in one or both of the premises of the established forms. In the majority of cases, he follows the same pattern of proof he used in the corresponding non-modal case to see whether they yield a conclusion in the corresponding modal case. This of course requires modal versions of the conversion rules. Proof through impossibility raises special difficulties in the modal syllogistic, and Aristotle sometimes uses a modal form of *ekthesis* in its place (see later in this chapter for further discussion of this point). As in the non-modal case, he proves invalidity by providing countermodels, though these differ in form from those for the non-modal syllogistic. The modal syllogistic resulting from these additions, presented in *Prior Analytics* I.8–22, is considerably more complicated than the non-modal syllogistic. It is also far more problematic to interpret, as commentators since ancient times have noted.

### Modal conversion rules

Aristotle says that necessity premises convert in the same way as non-modal premises:

Necessarily AeB |- Necessarily BeA
Necessarily AiB |- Necessarily BiA
Necessarily AaB |- Necessarily BiA

His arguments for these in *Prior Analytics* I.3 are parallel to his arguments for the non-modal cases in I.2. For necessary-e, he says:

If it is necessary for A to belong to no B, then it is also necessary for B to belong to no A. For if it were possible to some, then A would be possible to some B. (25a29–32)

335

***

Robin Smith

For necessary-a and necessary-i, he says:

If A belongs of necessity to every or to some B, then it will be necessary for B to belong to some A. For if it is not necessary, then neither would A belong of necessity to some B. (29a32–34)

The first argument assumes “possibly B to some A” is the denial of “necessarily B to no A,” so Aristotle is apparently following the (now-standard) understanding that “not necessarily” is equivalent to “possibly not” and treating “necessarily” and “possibly” as sentential operators:

¬□(BeA) ↔ ◊ ¬ (BeA) ↔ ◊(BiA)

However, in his subsequent discussions of the conversions of possibility sentences (*Prior Analytics* I.13), Aristotle adopts an account of possibility that is inconsistent with this (I will return to the latter point later). In addition, as interpreters since the Middle Ages have noted, “Necessarily A belongs to B” may be taken to mean either “The property of being necessarily A belongs to B” (the *de re* reading) or “The proposition that A belongs to B is necessary” (the *de dicto* reading). This distinction is a matter of the scope of the modal operator. In what follows, I will use parentheses to indicate it, as follows:

N(AaB) = □∀x(Bx→Ax) (wide scope, *de dicto*)
NAaB = ∀x(Bx→□Ax) (narrow scope, *de re*)
N(AiB) = □∃x(Bx&Ax) (*de dicto*)
NAiB = ∃x(Bx&□Ax) (*de re*)
N(AeB) = □∀x(Bx→¬Ax) (*de dicto*)
NAeB = ∀x(Bx→□¬Ax) (*de re*)
N(AoB) = □∃x(Bx&¬Ax) (*de dicto*)
NAoB = ∃x(Bx&□¬Ax) (*de re*)

Aristotle’s conversion rules are valid on the *de dicto* reading, since they follow from the conversion rules for non-modal sentences, e.g. since AeB |- BeA, N(AeB) |- N(BeA). However, they are not valid on the *de re* reading. (NA)eB, for instance, says that nothing that is B is necessarily A, from which it follows that nothing that is necessarily A is B; however, the latter does not entail “Nothing that is A is necessarily B.”

### The two understandings of possibility premises

The conversion rules Aristotle gives for premises asserting possibility differ radically from the corresponding non-modal rules. In *Prior Analytics* I.13, he first takes note of two ways “possible” may be understood: as “not necessarily not” (a sense he also recognizes in *On Interpretation*) and as “neither necessarily true nor necessarily false.” He then chooses the latter rather than the former as his preferred definition, so that it is equivalent to “Possibly A does not belong to B.” This might be expressed in the following schema:

◊Ax ↔ ◊ ¬ Ax

336

***

*Ancient Greek modal logic*

From this, Aristotle concludes that all possibility sentences are equivalent to their opposites; that is, each affirmative sentence is equivalent to the corresponding negative sentence:

Possibly A belongs to every B -|- Possibly A belongs to no B
Possibly A belongs to some B -|- Possibly A does not belong to some B

Combined with the previous principle, these make sense if we understand possibility sentences *de re*. For the universal case, we have:

Possibly A belongs to every B = ∀x(Bx → ◊Ax) = (PA)aB

But since ◊Ax entails ◊¬Ax, we have:

(PA)aB = ∀x(Bx → ◊Ax) ↔ ¬∀x(Bx → ◊¬Ax) = (PA)eB

Similarly,

(PA)iB = ∃x(Bx & ◊Ax) ↔ ¬∃x(Bx & ◊¬Ax) = (PA)oB

Consequently, says Aristotle, all possibility premises are “affirmative in form” and follow the conversion rules corresponding to affirmative non-modal sentences. However, they also follow the additional a-e and i-o rules indicated earlier.

This has major consequences for Aristotle’s modal logic. First, given his understanding of possibility, we no longer have the equivalences between “possibly” and “not necessarily not” or between “necessarily” and “not possibly not”: “A possibly belongs to B” is inconsistent both with “A necessarily belongs to B” and with “A necessarily does not belong to B.” Consequently “x is not necessarily A” is not equivalent to “x is possibly not A” but rather to the disjunction “either x is necessarily not A or x is possibly not A” (where the latter is equivalent to “either x is necessarily not A or x is possibly A”). Similarly, the denial of “x is possibly A” is “either x is necessarily not A or x is necessarily A.” These disjunctions are not expressible as categorical sentences. Aristotle is aware of this, as is clear from his treatment of the modal forms of Baroco and Bocardo (see later in this chapter). They also prevent him from using proofs through impossibility in the same way as in the non-modal case. Instead, he substitutes proofs by *ekthesis* for syllogisms with necessary premises, while in the case of possible premises he does use a necessary premise as the *reductio* hypothesis but then notes (correctly) that the conclusion asserts “possibility not in accordance with our definition” (see later in this chapter). He never makes use of a premise asserting “possibility not in accordance with our definition.”

Given his definition of possibility, Aristotle expands his modal syllogistic with all the forms that result from substitutions of possible-e for possible-a and of possible-o for possible-i premises and conclusions.

### Aristotle’s modal proofs

Aristotle then proceeds to investigate premise combinations involving at least one modal premise. His approach is to consider only those combinations he has already included in the non-modal syllogistic, determining whether the same categorical type of conclusion follows in the modal case and, if so, with what modality (though he does include a number of additional forms that result from the substitution of possibility premises as noted earlier). He considers, in order: (1) cases with two necessary premises; (2) one necessary and one assertoric

337

***

Robin Smith

(non-modal) premise; (3) two possible premises; (4) one possible and one assertoric premise; (5) one necessary and one possible premise. In general, he provides proofs, where possible, that follow the patterns used in the non-modal case but with the application of modal conversion rules. As before, he provides countermodels to show the invalidity of invalid forms, but these are now usually single term-triples showing, not that no conclusion follows, but instead that a conclusion of a certain modality does not follow. The details are both complex and difficult to interpret. In what follows, I will describe a particular syllogistic form by giving its medieval name followed by a series of letters indicating the modalities of the two premises and conclusion: for instance, “Barbara NAN” means “A syllogism in the form Barbara with a necessary major premise, an assertoric minor premise, and a necessary conclusion.”

Aristotle begins with a quick treatment of all the NN cases: for each valid form in the non-modal syllogistic, the corresponding NNN form is valid and, with two exceptions, proofs are exactly analogous to those for the non-modal cases, since analogous conversion rules hold for N sentences (*Prior Analytics* I.8). The exceptions are the two cases requiring proofs through impossibility in the non-modal case (that procedure is not available because of Aristotle’s somewhat complicated views on possibility sentences). A proof by *ekthesis* for Baroco NNN would be as follows:

Necessarily BaA	premise
Necessarily BoC	premise
Necessarily CaX	2, N-o-ecthesis
Necessarily BeX	2, N-o-ecthesis
Necessarily XeB	4, conversion
Necessarily XeA	1, 5 Barbara NNN
Necessarily AeX	6, conversion
Necessarily AoC	3, 8, Felapton NNN

Steps 5 and 7 here rely on necessary-e conversion, which as noted previously requires a *de dicto* reading. Steps 3 and 4 require a modal version of e-ecthesis:

If necessarily BoC, then for some part of C (say X), necessarily BeX and necessarily CaX.

Since Aristotle’s proofs of the conversion rules of necessary premises appear to require the *de dicto* reading, so will all these proofs. However, his treatment of AN and NA cases appears to be inconsistent with this. He says that for first-figure syllogisms, a necessity conclusion follows when it is the major premise that is necessary, but that only an assertoric conclusion follows when it is the minor premise that is necessary:

Necessarily AaB, BaC |- Necessarily AaC
AaB, Necessarily BaC |- AaC only
Necessarily AeB, BaC |- Necessarily AeC
AeB, Necessarily BaC |- AeC only

He defends the first of each pair (NAN) as follows:

Since A belongs, or does not belong, of necessity to every B and C is one of the Bs [τι τῶν Β], it is obvious that it [A] will be of necessity in one or the other of these relations [ἔσται θάτερον τούτων] to C.
(30a21–23)

338

***

*Ancient Greek modal logic*

This language strongly recalls that used in I.4 to justify Barbara AAA and Celarent AAA and appeals directly to his definition of “belongs to all/belongs to none.” He rejects the corresponding ANN cases as follows:

1. Suppose AaB, Necessarily BaC |- Necessarily AaC
2. Necessarily AaC, Necessarily BaC |- Necessarily AiC (*Darapti* with necessity premises, already established)
3. AaB, Necessarily BaC |- Necessarily AiC (1 and 2)
4. However, 3 is invalid (shown by a counterexample)
5. Therefore, 1 is invalid (since with 2, known to be valid, it yields the invalid 3)

We can preserve Aristotle’s distinction between the NAN and the ANA cases here if we adopt a *de re* reading for the necessary premise (and conclusion)/explanation for Aristotle’s distinction between “the two Barbaras” is that he treats “necessarily A” and “A” as distinct predicates. Using “NA” for “necessarily A,” we then have:

(NA)aB, BaC |- (NA)aC: valid (*Barbara* with terms NA, B, and C)
AaB, (NB)aC |- (NA)aC: invalid since it contains four distinct terms (NA ≠ A)

However, this interpretation calls into question the validity of Barbara NNN:

(NA)aB, (NB)aC |- (NA)aC : invalid, since it contains four terms

We might remedy this by supposing that NB implies B, which Aristotle appears to accept elsewhere, though he does not mention it in this context. However, the problem remains that Aristotle’s acceptance of Barbara NAN seems inconsistent with the *de dicto* reading, while his conversion rules for necessary propositions seem inconsistent with the *de re* reading. This problem—the “two Barbaras” problem—is the most widely discussed issue in interpreting Aristotle’s modal syllogistic.

There are other related problems. Aristotle says that both Baroco ANN and Baroco NAN are invalid. For Baroco ANN, he uses the same countermodel he used earlier for Camestres NAN, concerning which he says this:

Let A be animal, B human, C white, and let the premises be taken similarly. For it is possible for animal to belong to no white. Then human will not belong to any white either, but not of necessity, for it is possible for there to be a white human (though not as long as animal belongs to nothing white).

The example, as given for Camestres ANN, is as follows:

Suppose a situation in which animal belongs to no white (i.e. that there are no white animals). Then, since every human is (of necessity) an animal, it would follow that in that situation nothing white is a human. However, it is not the case that in that situation, it would be necessary that nothing white is a human.

This counterexample is quite different in form from Aristotle’s usual counterexamples, which consist of two sets of three terms such that, when substituted for the terms in a putative syllogism, result in a true universal (and necessary, in the case of modal premises) affirmative

339

***

Robin Smith

conclusion in one case and a true universal (and necessary, in the case of modal premises) negative conclusion. Here, he simply appeals to the claim that “it is possible for there to be a white human.” One might object as follows: in a situation in which there are no white animals, everything that is white will be something other than an animal; but surely, whatever is not an animal is *necessarily* not a human (e.g. a white stone is necessarily not a human, even if it is not necessarily white). Therefore, in a situation in which there are no white animals, each thing that is white is something that is necessarily not a human.

Furthermore, proofs using *ecthesis* can be given for both Baroco ANN and Bocardo NAN in the same way as for the NNN cases. The proof for Baroco ANN:

BaA	premise
NBoC	premise
CaX	2, ecthesis
NBeX	2, ecthesis
NXeB	4, conversion
NXeA	1, 5 Barbara NAN
NAeX	6, conversion
XiC	3, conversion
NAoC	7, 8, Ferio NAN

However, Aristotle rejects Baroco ANN and Baroco NAN with countermodels, which contradicts this.

In the case of Camestres NAA, Aristotle offers two additional arguments that a necessity conclusion does not follow. First (30b21–24), he follows the non-modal proof and notes that the corresponding form Celarent ANN is not valid, though Celarent NNN and NAA are valid. This is not so much a proof of invalidity as an argument that a specific proof for validity cannot be given. Second (30b24–31), he argues that if Camestres NAN were valid, then Felapton ANN would be valid, but (as he shows by a countermodel) it is not. For suppose NAaB, AeC |- NBeC to be valid:

NAaB	premise
AeC	premise
NBeC	1,2, Camestres NAN (assumed to be valid)
NCeB	3, conversion
NBiA	1, conversion
NCoA	4,5 Ferio NNN

Thus, we can deduce AeC, NAaB |- NCoA (Felapton ANN) using Camestres NAN. However, says Aristotle, “nothing prevents something having been taken as A such that C possibly belongs to every A.” He illustrates this with a counterexample: if we suppose that there are no white animals, it still might be the case that every animal is possibly white (that is, we can suppose that every animal in such a situation has the possibility of becoming white).

### Syllogisms with possible premises

Aristotle’s account of syllogisms with possibility premises is both much more complex and more problematic. In general, he treats “possibly A” and “A” as distinct predicates (I will represent “possibly A” here as PA), which seems congenial to a *de re* reading. However, given his definition

340

***

*Ancient Greek modal logic*

of possibility, PA is logically independent from A: something may be possibly A whether or not it is A, and something may be A whether or not it is possibly A. Consequently, whatever is necessarily A is both not possibly not A and also not possibly A, in Aristotle’s defined sense, and likewise what is not possibly A is both not possibly A and not possibly not A. In this section, I will use P(Q) (for example, P(AaB)) to represent a proposition expressing possibility “not according to the definition,” that is, a denial of a necessary proposition.

To begin with, Aristotle accepts the following inference forms as valid:

PAaB, PBaC |- PAaC
PAaB, BaC |- PAaC
AaB, PBaC |- P(AaC) (the conclusion here is “possible not in accordance with our definition”)

He says the first two are “complete” (“evident from the definition of possible”). On a *de re* interpretation, Barbara PAP should be valid for the same reason as Barbara NAN. However, in the case of Barbara PPP, the reasoning that could be applied to Barbara NNN does not apply, since P(p) does not entail p. Instead (and remarkably), Aristotle adds the stipulation that “A possibly to every B” is to be understood as “A belongs to everything to which B possibly belongs.” On this understanding, Barbara PP amounts to PAaPB, PBaPC |- PAaPC, which is valid as a non-modal Barbara. However, in the case of Barbara PNP, Aristotle instead appears to treat the major premise as PAaB:

For since C is below B and A is possible to every B, it is evident that it will be possible to every C. (33b34–36)

Because of this, the interpretation of Aristotelian possibility sentences is unclear: does he prefer the ampliated reading, or the unampliated reading, or does he switch between the two—and if so, on what principles?

Aristotle’s treatment of Barbara AP is considerably more complex, and indeed it is perhaps the most intriguing, as well as the most difficult, section of his modal syllogistic. He begins by arguing for the following principle:

If when A is B then it is necessary for B to be, then if A is possible B will also of necessity be possible. (34a5–7)

This might be translated into modern formal logic in two ways:

P→Q |- ◊P→◊Q
□(P→Q) |- ◊P→◊Q

This is the only place in the syllogistic where Aristotle uses letters as sentential variables rather than predicate variables, and it also seems to countenance arguments with a single premise. In fact, Aristotle takes note of the latter point immediately, explaining that we should really understand P here as the premises of a syllogism (since, on his view, nothing follows from just one premise). It is also the only passage in the modal syllogistic to which Aristotle makes any reference outside *Prior Analytics* I.8–22 itself: he states it in *Metaphysics* Θ 3, in arguing against the Megarian position that only what is necessary is possible.

341

***

Robin Smith

Having stated his principle, Aristotle offers a proof for it (34a7–12) and then puts it to use in arguing for Barbara AP. His argument is an unusually structured proof through impossibility. He first derives another principle from it:

If we assume as true something which is false but not impossible, then whatever follows from that assumption may be false but will not be impossible. (34a225–27)

He then uses this principle to construct a proof for Barbara AP:

With these distinctions made, then, let A belong to every B but let B be possible to every C. Then it is necessary for A to be possible to every C. For suppose not, and suppose B as belonging to every C (this is false but not impossible). Then since A is not possible to every C but B belongs to every C, A will not be possible to every B (for a syllogism comes about through the third figure). But it was assumed to be possible to belong to every B. Then necessarily A will be possible to every C, since when something false but not impossible was assumed the result was impossible. (34a34–b2)

As Aristotle notes, the conclusion here is the denial of the *reductio* hypothesis “A is not possible to every C,” which he interprets as NAeB; consequently, it does not express “possibility in accordance with our definition” but rather the denial of NAeB, that is M(AeB). Both the nature of the principle Aristotle uses here and the structure of his argument for APM are exceptionally difficult to interpret (see Waterlow 1982, Fine 2011, Rini 2011, Malink & Rosen 2013).

### Models of the modal syllogistic

An extensive literature on the interpretation of Aristotle’s modal logic has developed over the past eight decades. I note here only a selection of these. The earliest such interpretation (Becker 1933) argued that Aristotle in effect employed the distinction between *de re* and *de dicto* readings of modal sentences without realizing it, leading to an inconsistency in his system (Becker also saw other inconsistencies). McCall (1963) gives a formal interpretation of a subset of Aristotle’s results based on a non-formal interpretation advanced by Nicholas Rescher; Johnson (1994) gives a semantics for it. Nortmann (1996) models Aristotle’s system in predicate logic and argues that its necessity is S4 necessity. Patterson (1995) gives a comprehensive but less formal reconstruction the foundation of which is an interpretation of Aristotelian modal sentences as containing “modal copulas.” While most of these models make corrections in Aristotle’s system to obtain coherence or limit themselves to a subset of his results, some more recent reconstructions aim at reproducing as much as possible and at modeling his proofs as well as his results. Rini (2011) does so by explaining apparent inconsistencies in Aristotle’s understanding of modals on the basis of a semantic distinction of terms. Malink (2013) succeeds in reproducing every detail of Aristotle’s results, though at the cost of much greater complexity.

### References

Anscombe, Gertrude Elizabeth. 1956. “Aristotle and the Sea Battle,” *Mind* 65: 1–15.
Becker, Albrecht, 1933. *Die Aristotelische Theorie der Möglichkeitsschlüsse*. Berlin: Junker und Dunnhaupt.
Bobzien, Susanne. 1993. “Chrysippus’ Modal Logic and Its Relation to Philo and Diodorus,” 63–84 in K. Döring and T. Ebert, eds., *Dialektiker und Stoiker* (Stuttgart: F. Steiner).

342

***

*Ancient Greek modal logic*

Bobzien, Susanne. 2011. “Dialectical School.” in Edward N. Zalta, ed., *The Stanford Encyclopedia of Philosophy* (Fall 2011 edition), URL: https://plato.stanford.edu/archives/fall2011/entries/dialectical-school/.
Corcoran, John. 1972. “Completeness of an Ancient Logic,” *Journal of Symbolic Logic* 37: 696–705.
Corcoran, John. 1974. “Aristotle’s Natural Deduction System”. in J. Corcoran, ed., *Ancient Logic and Its Modern Interpretations*. Dordrecht: D. Reidel, 85–131.
Döring, Klaus. 1972. *Die Megariker: kommentierte Sammlung der Testimonien*. Amsterdam: B. B. Grüner Verlag.
Döring, Klaus. 1989. “Gab es eine Dialektische Schule?” *Phronesis* 34: 293–310.
Ebert, Theodor. 2008. “In Defence of the Dialectical School.” in F. Alesse, ed., *Anthropine Sophia. Studi di filologia e storiografica filosofica in memoria di Gabriele Giannantoni*. Naples: Bibliopolis, 275–293.
Fine, Kit. 2011. “Aristotle’s Megarian Manoeuvres,” *Mind* 120: 993–1034.
Frede, Dorothea. 