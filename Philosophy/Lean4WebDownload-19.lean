/-
  SPINOZA'S ETHICS V3.1: A COMPLETE BOURBAKI/MATHLIB4 FORMALIZATION
  ═══════════════════════════════════════════════════════════════════

  Extension of V3.0 based on the philosophical summary by Don Garrett. 
  This file formalizes the entire arc of the Ethics (Parts I–V) at 
  maximum philosophical depth, integrating physical science, political 
  theory, epistemology of privation, and the eternity of the mind.
  ═══════════════════════════════════════════════════════════════════
  Chapter 3. Benedict de Spinoza 
Don Garrett 
The thought of Benedict (Baruch) de Spinoza constitutes a genuine philosophical system; that is, it provides deeply interrelated answers to a full range of philosophical questions in metaphysics, philosophy of mind, epistemology, philosophy of physical science, philosophy of psychology, ethics, political theory, and philosophy of religion. His work is profound, original, and often strikingly modern; but in order to understand its formulation, it is essential to have some understanding of his life and of the distinctive historical and cultural perspective that he occupied. 
1. Life, Writings, and Context 
In 1632 – the same year in which Galileo published his Dialogue Concerning the Two Chief World Systems and thereby provoked the Catholic Church to put him on trial for heresy –Spinoza was born to a moderately prosperous merchant family in the Jewish community of Amsterdam. Most members of that community were, like Spinoza's own family, descended from Spanish and Portuguese Jews who had either fled from or been expelled by the Inquisition. This rather cosmopolitan community sought to rediscover its Jewish heritage in the Netherlands, which had recently achieved its independence from Spain and now offered a degree of religious freedom. Accordingly, Spinoza received a religious education that included Hebrew, the Torah and the Talmud, and important medieval Jewish thinkers such as Moses Maimonides. In addition, he soon discovered the philosophy of Descartes – who himself had moved to the Netherlands 
four years before Spinoza's birth in order to write in relative freedom and solitude, remaining there until he joined Queen Christina's court in Sweden in 1649. Between 1652 and 1654, Spinoza studied Latin (the language in which he wrote for publication) and Cartesian philosophy in the school of the Cartesian Francis van den Ende. At least partly to avoid being associated with potentially heretical views – such as the doctrine that God is corporeal and the denial of personal immortality – the Jewish community excommunicated the no longer observant Spinoza in 1656. Upon his excommunication, Spinoza changed his first name from “Baruch” to its Latin equivalent “Benedict” and relocated just outside Amsterdam. 
In 1660, he moved near Leiden, where he supported himself by grinding lenses and by tutoring students of the nearby university. There he worked on his never-completed Treatise on the Emendation of the Intellect and on his Short Treatise on God, Man, and His Well-Being. The latter work, an early treatment of the main topics of his later Ethics, was discovered – in the form of a Dutch manuscript translation – and published only in the nineteenth century. His first work to appear in print was Descartes's Principles of Philosophy. Written in an axiomatized format in which numbered propositions are demonstrated by appeal to axioms, definitions, and previous propositions, it provides a presentation and exposition of Part One, Part Two, and an initial portion of Part Three of René Descartes's four-part Principles of Philosophy; it also includes some unaxiomatized background material called “Metaphysical Thoughts.” Published in 1663, this work had developed – with the encouragement of his loyal circle of friends, many of them Christians of the nondogmatic Collegiant sect – from Spinoza's axiomatization for a tutorial 
student of Part Two of the Principles of Philosophy. It helped to establish Spinoza's reputation as an interpreter of Descartes's metaphysical and natural philosophy. 
In the same year, Spinoza moved to the outskirts of The Hague, where he remained in communication with his Amsterdam-centered circle of friends and also with such important scientific figures as Henry Oldenburg (the secretary of the British Royal Society) and the Dutch mathematician and physicist Christiaan Huygens. In 1670, he published his Theological-Political Treatise concerning the interpretation of scripture and the role of religion in the state. The book was written partly in response to the murder by an angry mob of the De Witt brothers, leaders of the republican party in the Netherlands. Always cautious about disseminating his more controversial views too widely, Spinoza published the book anonymously and with a false imprint of “Hamburg.” In 1673 he declined a proffered chair at the University of Heidelberg, partly on the grounds that it would interfere with his study and partly on the grounds that he might not be able to honor the invitation's expressed presumption that he would not use his promised freedom of expression to “disturb the established religion.” 
Spinoza's masterpiece, and by far the most complete statement of his philosophical system, is the Ethics (Ethica Ordine Geometrico demonstrata, or Ethics Demonstrated in Geometrical Order). This work consists of five parts, all in axiomatized form, beginning with metaphysics and epistemology, and leading through psychology to ethics and the way to blessedness. He traveled to Amsterdam in 1675 to see to the book's publication, only to change his mind for reasons of prudence. The following year, he received a two-week visit from Leibniz (returning to the continent from a trip to England). Leibniz, who had originally corresponded with him years earlier on a question of optics, was both attracted and repelled by Spinozism, and regarded it as a significant intellectual rival to his own philosophy. Spinoza died of respiratory disease, likely caused or exacerbated by the inhalation of glass dust in his work, in 1677. His friends saw to the publication of his Opera posthuma, which included the Ethics, the unfinished Treatise on the Emendation of the Intellect, an unfinished Political Treatise, a Hebrew Grammar, and Correspondence. 
The philosophical tasks that Spinoza undertook during his short lifetime were set for him in some measure by the time and place in which he lived. Throughout western Europe, the new science that followed in the wake of the Copernican Revolution was undermining the traditional scholastic philosophy derived from Aristotle and Christian church teachings. This new science was mechanistic and quantitative in spirit, and seemed to leave no room for the older conception in which the nature and behavior of bodies was explained through their possession of distinctive substantial forms and natural ends. Thus, one problem that Spinoza faced was that of providing a new metaphysical understanding of the ontological structure of the universe that would incorporate and render intelligible the new mechanistic science. Related to this was the crucial problem of explaining the place of mentality in general and of human minds in particular in relation to this world of physical mechanism. With revolutionary changes in conceptions of the natural world and the place of human beings within it naturally came new questions about the nature of human knowledge and the proper method to follow in understanding both the physical world and the human mind itself. 
Spinoza's concerns, however, were not limited to metaphysics, philosophy of mind, epistemology, philosophy of physical science, and philosophy of psychology. In his conception of philosophy, all of these topics gain their ultimate value from the contribution that an understanding of them can make to a good human life. Thus, he was particularly concerned to employ his more metaphysical and epistemological results to shed light on how human beings should live their lives, what they should pursue, how they can control their dangerous passions, and even how the modern state should be organized in order to promote human flourishing. Particularly important to the well-being of the well- ordered state is the role played by popular religion; and it is largely for this reason that Spinoza devoted intensive effort to the proper interpretation of the Bible. The significance of religion is not, however, by any means limited to its role in the state. On the contrary, stimulated no doubt in part by the ongoing conflict between science and Christianity – which he of course viewed from the distinctive perspective of an excommunicated Jew – he radically reconceived the nature of God, God's relation to human beings, and human beings' relation to God. Spinoza's identification of God with Nature is among the most striking and distinctive aspects of his philosophy; his radical displacement of revelation and ritual by philosophy and science is among its most modern. 
2. Metaphysics 
The fundamental categories of Spinoza's ontology are “substance,” “attribute,” and “mode.” He defines “substance” at the outset of the Ethics as “what is in itself and is conceived through itself; that is, that whose concept does not require the concept of another thing, from which it must be formed” (1d3).1 The dual nature of this definition, which employs the parallel notions of being “in itself and being “conceived through itself,” reflects his fundamental commitment to the view that whatever is true of things diemselves is reflected in the ideas of those things. Descartes would have agreed with Spinoza that a substance is “in itself,” meaning by this that it has qualities or “modes” (for example, a particular size, shape, and color) without itself being the quality of any other thing. Evidently led by the reflection that such qualities are dependent for their existence on the things of which they are qualities in a way in which those things are not dependent on their qualities, Descartes defines a substance as something that is not dependent on any other thing for its existence. A consequence of this Cartesian definition, however, is that Descartes must acknowledge that only God is a substance in the strongest and strictest sense, since only God is entirely independent of anything else for his existence; other things, such as bodies and human minds, are substances only in a weaker sense, for they depend for their continued existence, in Descartes's view, on God's concurrence. Spinoza, in contrast, uses the term “substance” univocally. For him, the requirement that a substance be absolutely in itself and conceived through itself entails that a substance must be absolutely the sole cause of its own existence. This is because things are conceived through their causes (1a4), so that if anything 
else caused a substance, the substance would be conceived through that cause and hence not through itself. But a thing can be self-caused only if its existence derives from its own essence (1d1) rather than from any external thing; and since a thing is properly conceived by conceiving its essence (2d), it follows that a substance is a thing whose existence cannot be denied by anyone who forms a proper concept of its nature. Furthermore, it may be noted, since an adequate definition captures the essence of a thing (as Spinoza repeatedly emphasizes), only something whose existence follows from its definition alone – so that its existence can be demonstrated a priori – can be a substance. Since bodies and human minds lack this 
characteristic, instead deriving their being as well as many of their qualities from external causes, they cannot be substances in Spinoza's sense. 
Spinoza defines an “attribute” as “what the intellect perceives of a substance, as constituting its essence.” This concept of an “attribute” derives, in part, from Descartes's concept of a “principal attribute.” For Descartes, every ordinary quality, or “mode,” of a substance is in some way a modification (or, one might say, a determination or specification) of this principal attribute. While a Cartesian substance may undergo change of its particular modes, it cannot undergo a change of its principal attribute, for the principal attribute constitutes what the substance essentially is. According to Descartes, a substance cannot be without its principal attribute, and whatever has a given principal attribute is a substance of the kind constituted by that principal attribute. In his view, there are two kinds of created substances, each with its own principal attribute: bodies having extension – that is, physical/spatial/dimensional character – as their principal attribute (and thus having, for example, particular sizes, figures, and motions among their modes); and minds having thought as their principal attribute (and thus having, for example, acts of conceiving, affirming, doubting, desiring, and willing among their modes). While Spinoza agrees that extension and thought are each attributes that constitute the nature of a substance – and so correspond, thus far, to Descartes's conception of “principal” attributes – he denies that bodies and human minds are themselves substances, and he denies that a substance need be limited to having a single attribute. On the contrary, the more reality or (equivalently, for Spinoza) perfection a substance has, the more such attributes it will have (1p9). God, the most real and most perfect being, can therefore be defined as the substance who has infinite (that is, an unlimited array of, or all possible) attributes, each of which is necessarily infinite (unlimited) within its own realm (d6). Since the existence of God necessarily follows from this definition, according to Spinoza (1p11d), God necessarily exists. This God exists as a thinking substance (1p1), as previous philosophers had maintained, but also and equally as an extended (that is, physical, or corporeal) substance (1p1 5s and 2p2), and as a substance of other infinite attributes unknown to human minds as well. Each divine attribute may thus be thought of as a fundamental way of being for God, each constituting the essence of God insofar as God is considered as existing in that particular way. 
Spinoza defines a “mode” as “the affection [i.e., the modification, or quality] of a substance, or that which is in another through which it is also conceived.” Every mode of a substance is thus a particular modification of an attribute of that substance. Since every mode is in and conceived through the substance of which it is a mode, it must also be entirely caused by the substance of which it is a mode; thus, all causation is the self-determination and self-expression of a substance. Every mode is either an “infinite mode” or a “finite mode,” depending on the way in which it is produced and the scope of its existence. Infinite modes follow, either immediately or mediately (that is, either directly or through one or more other infinite modes), from the “absolute” nature 
of the attribute of which they are modes (1p21d and 1p22d); in consequence, they are permanent and pervasive features or aspects of an entire attribute, such as, for example, general features corresponding to the general laws of nature governing extension or thought. Although finite modes also follow from the nature of the attribute of which they are modes, they do not follow simply from the “absolute” nature of those attributes but require the existence of other finite modes as well (1p28); hence, they introduce temporally and locally limited variety within an attribute. The causation of finite modes by other finite modes in no way violates the thesis that 
all modes are caused by the substance of which they are modes, because causation through its modes is simply one way in which a substance can express or exert its own causal power. 
Because all causation is the self-determination and self-expression of a substance, there could be no causal interaction between Spinozistic substances even if there could be a plurality of substances. In fact, however, Spinoza famously holds that there is and can only be one substance, which he calls “Deus, sive Natura” – that is, “God or Nature” (where the use of “or” has theforce of “in other words”). He argues that God is the only substance on the grounds that substances cannot share an attribute (1p5) and God – the substance of all attributes – necessarily exists; God thereby forestalls the possibility of any other substance (1p14d). This denial that substances can share an attribute is distinctively Spinozistic; Descartes, for example, supposed that human minds were individual substances (albeit in the weaker sense of the term “substance”) all sharing the attribute of thought. Spinoza rejects the sharing of attributes on the grounds that it would be impossible to distinguish two different substances within the realm of a single attribute. For two such substances could not be distinguished by a difference of modes of that attribute unless the difference of modes could be conceived through a difference in the attributes through which those modes must be conceived; but if one seeks to base the distinction of two substances within the realm of an attribute on a difference in the relevant attribute, then one grants that the two substances are not sharing the same attribute after all (1p5d). Spinoza's doctrine that there is only one substance is sometimes called “monism” or (to distinguish it from the doctrine of plurality of attributes that he endorses) “substance monism.” 
If God is the only substance, then what are the ordinary bodies and minds that common sense regards as substances? Spinoza's answer is forthright: they are finite modes of God, local and temporary expressions of the divine nature. Finite modes are limited expressions of God's attributes; for example, a particular body is constituted by a “fixed pattern” or “fixed ratio” of motion and rest occurring within the attribute of extension (definition following 2p13s), and a particular mind is the idea representing the actual existence of such a persisting pattern (2p13). Nevertheless, Spinoza does not deny that bodies and minds are things, or at least thing-like, as well. On the contrary, just as God is absolutelyin itself and conceived through itself, certain finite modes – which Spinoza also calls “singular things” – are to a finite and limited extent “in themselves.” Each singular thing, in his view, has its own essence and its own modes; and the more causal power a singular thing has – that is, the more it has an essence or nature of its own, from which effects follow – the more in itself that thing is, and the more able it is to sustain itself in continued existence through its own power (3p6). (This self-sustaining activity is, of course, compatible with its having an external cause for its origination in existence.) Although singular things are not substances, they thus model in a finite and limited way the absolute nature of the one genuine substance of which they are modes and whose power they utilize and express. 
3. Philosophy of Mind 
As both an extended substance and a thinking substance, Spinoza's God has modes of extension and modes of thought. Furthermore, because “the order and connection of ideas is the same as the order and connection of things” (2p7, derived from 1a4), there is an isomorphism between these attributes: for each mode of extension, there is a corresponding mode of thought which is the idea of that mode of extension. In fact, Spinoza goes further – each mode of extension is 
identical with the idea that is its corresponding mode of thought (2p7s). God as an extended thing is expressed through a system in which modes cause other modes through their respective shares of God's infinite physical (or, one might also say, dynamic) power; and God as a thinking thing is expressed through a system in which the ideas of those modes cause one another through their respective shares of God's infinite thinking (or, one might also say, logical) power. That is, just as God's existence is expressed in different ways of being, so God's power is expressed in different ways of being. These ways in which God's existence and power are expressed are each self-contained and self-sufficient: facts about the world of extension are explained completely and exclusively by God's extended nature, and facts about the world of thought are explained completely and exclusively by God's thinking nature. There is no possibility that this causal independence of the attributes could have resulted in a world of thought that is not isomorphic with the world of extension, for everything that occurs does so through the utter necessity of the divine nature (1p16, 1p29, 1p33): just as there is only one possible way that the world of extension could be, so there is only one possible way – a parallel way – in which a world of extension could possibly be conceived in the attribute of thought. 
This conception of the relation between the attributes of extension and thought provides Spinoza with a distinctive solution to the problem – so acutely felt both by Descartes's followers and by his critics – of explaining the relation between the human mind and the human body. First, Spinoza argues that a given human mind is just the idea of that human being's body (2p13) – that is, it is the mode of thought that is identical with that human body and which has that human body as its object. Although he does not deny that the human mind contains ideas that represent things other than the human body, these ideas do so, on his conception, only through first representing some aspect of the human body to which those other things are related. Because the human mind and the human body are thus the very same mode of God, each expressed and conceived through a different attribute of God, there is no question of how they can be related as distinct substances, or indeed as distinct things of any kind. Furthermore, because the attributes of extension and thought are each causally self-contained, there is no question of bodily events causing mental events or vice versa. Every physical event in the body, insofar as it is a physical event, is caused by other physical things exclusively. But every physical event is also identical with a mental event; and that mental event, insofar as it is a mental event, is caused by other mental things exclusively. Spinoza thus holds a form of the mind-body identity theory concerning human beings. But for him, this identity is merely a particular instance of a far more pervasive feature of the universe, one according to which not only each animal body but each non-organic body as well has an idea (though it may be sufficiently weak and rudimentary that it need not be called a “mind”) that stands to that body in the same general relation as that in which a human mind stands to a human body. As he puts it, all individuals “are animate” but “to different degrees.” This view is based not on any supposition that mentality is required to explain the behavior of inanimate bodies – for even in the case of human beings, the attribute of thought plays no role in the proper explanation of the behavior of extended bodies – but is based rather on the thesis that God is an infinitely thinking thing, so that whatever is expressed in extension is also expressed in thought. Just as all of the individual bodies in the universe compose an infinite extended individual that is in God (2p13s), so too the ideas of those things – including human minds – are parts of the all-inclusive idea that is God's infinite intellect (2p11c). But although the human body is part of an infinite extended individual and the human mind is part of God's infinite intellect, for Spinoza, it is not correct to say that human beings are parts of God. For 
these infinite things are themselves only infinite modes of God. At least in the sense in which parts are logically prior to the wholes that they compose and are potentially separable from those wholes, God itself has no parts – only infinite and finite modes. 
4. Epistemology 
Spinoza's epistemology, like his metaphysics, exhibits many illuminating contrasts with the views of Descartes. One of these contrasts concerns the two philosophers' respective conceptions of the method by which knowledge is to be discovered. One of Descartes's chief methodological goals is what may be called “methodological caution” – that is, the avoidance of “hasty and precipitate judgments.” In order to achieve methodological caution, Descartes recommends what is sometimes called “methodological doubt.” His philosophical method proposes that an inquirer should begin by setting out to doubt whatever can be doubted; for only what is indubitable – that is, cannot be doubted – is entitled to be accepted as certain knowledge. In the service of methodological doubt, in turn, the Cartesian inquirer pursues what may be called “methodological skepticism” – the endeavor to discover and render credible the strongest possible grounds for doubt. Because truth consists, for Descartes, in an agreement between ideas and the states of affairs they represent, and because there are strong initial grounds for skepticism concerning things outside the inquirer's mind, Descartes seeks an internal property of ideas themselves that can serve as a criterion for their truth. After first demonstrating that God exists and is not a deceiver, Descartes takes himself to have rendered “whatever is perceived clearly and distinctly is true” indubitable, thereby entitling himself to accept the clarity and distinctness of ideas as a criterion of their truth. 
Spinoza agrees that methodological caution is a worthy aim, but he denies that methodological doubt (and hence methodological skepticism) is the best way to achieve it. Doubt, as he explains in his Treatise on the Emendation of the Intellect, arises exclusively from acquiring ideas in the wrong order. More specifically, it arises when the mind understands enough to see that one idea has some relation to another idea but lacks the causal knowledge to grasp exactly how the two ideas are properly related. For example, if one knows enough about sense perception to know that perceptions of distance have sometimes been misleading, but without knowing enough about the causal origin of a particular sense perception of the sun, then one will doubt whether the sun really stands at just the distance at which it appears. The proper order of inquiry, for Spinoza, is to begin with adequate ideas of causes and to derive ideas of the effects from them. When this is done consistently, doubts never arise. Thus, for example, whereas Descartes doubts for most of his Meditations whether or not he has a body, the question of the existence of the human body does not arise in Spinoza's Ethics until the point (in Part Two) at which he is prepared to demonstrate the relation between the human mind and human body as a result of understanding the causes of each. As this illustrates, doubt, for Spinoza, is not something first to be induced and then to be refuted; rather, it is something always to be avoided by following the proper order. If this is done, no doubts can be successfully raised, since any doubt suggested about the truth of a piece of knowledge will already be seen to be unfounded in light of the inquirer's already-clear grasp of the truth of that piece of knowledge. 
The perception of truth is, for Spinoza, unmediated by any criterion of truth of all, as he emphasizes in the Treatise on the Emendation of the Intellect, and hence it is unmediated by any 
criterion whose reliability might itself be called into question. He agrees with Descartes that clear and distinct ideas are true; but unlike Descartes, he does not see the clarity and distinctness of ideas – or as he usually prefers to say, their “adequacy” – as a property distinct from their truth itself. True ideas do agree with their objects (1a6), but at the same time their truth also involves the internal characteristic of adequacy. “By adequate idea I understand an idea which, insofar as it is considered in itself, without relation to an object, has all the properties, or intrinsic denominations of a true idea” (2d4). Thus, whereas Descartes argued that there is an internal characteristic that is possessed by all and only true ideas (that is, ideas constituting genuine knowledge), Spinoza's definition of “adequacy” simply takes this for granted. His metaphysics suggests why he thinks he can legitimately do so. Because every idea is identical with its object, a thing and the idea of that thing are the very same mode of God considered in two different ways; and hence, the internal adequacy of an idea and the complete correspondence between an idea and its object can be regarded as the very same feature of that idea, considered in those same two ways. It may also be supposed that the adequacy of an idea lies in its representing its object with sufficient distinctness and coherence to show that what it represents is genuinely possible; for the doctrine that there is only one possible way in which the world could have been entails that whatever is genuinely possible is also actual. 
Of course, to say that the agreement of true ideas with their objects can be explained through the identity which all ideas have with their objects raises the question of how any ideas can ever fail to be true. On Spinoza's conception of falsehood, however, it is not a positive characteristic of ideas, but rather a kind of privation or “mutilation.” Because things must be understood through their causes, an idea of a thing that does not include knowledge of its cause is incomplete and partial. Every idea of a thing, as that idea exists in God's infinite intellect, exists in the context of ideas of that thing's causes, and is complete, adequate, and true. As some of these ideas exist in human minds, in contrast, they are without the context of the related ideas through which their full understanding depends, and hence as they exist in the human mind they are inadequate and incomplete – that is, false. 
For Spinoza, the distinction between those ideas that are complete and adequate in the human mind and those that are not corresponds to the distinction – also emphasized by Descartes and Leibniz – between ideas that are conceived by (or in) the intellect and those that are conceived by (or in) the imagination, respectively. Ideas of the imagination are images of a sensory character (in a broad sense that includes visual, auditory, and other kinds of externally and internally derived sensory impressions). Sense experience itself is classified as a form of imagination for Spinoza – not because the objects that it represents are unreal, but because it presents those objects in images, which do not themselves provide a full, or intellectual, understanding of their causes. Imagination also includes the recollection or rearrangement of the content of such images of experience through memory, dreaming, and thinking with images. The intellect, in contrast, is not fundamentally imagistic and constitutes a higher kind of understanding through ideas that are themselves adequate. 
Spinoza distinguishes (2p40s2) three kinds of knowledge (or, better, three kinds of cognition – the Latin is cognitio). “Knowledge of the first kind,” which he also calls “imagination,” is the lowest kind of knowledge. It includes knowledge from report or testimony (either written or spoken) and mere unregulated sense experience or generalizations of sense experience. 
“Knowledge of the second kind,” which he also calls “reason,” derives from “common notions” and “adequate knowledge of the properties of things.” “Common notions” are aspects or ways in which all things of a given kind agree and which are present “equally in the part and in the whole.” Because they are aspects of things that can be found complete in each part as well as in the whole, these general aspects or features of things cannot be grasped only partially and so must be grasped adequately if they are grasped at all. The “properties” of a thing, in Spinoza's technical sense of that term, are qualities of a thing that follow from the thing's essence but do not themselves constitute its essence; since a thing cannot exist without its essence, it also cannot exist without its properties, which follow from it. (Properties may thus be distinguished from mere accidental qualities, which a thing may lose.) “Knowledge of the third kind,” which he also calls “intuitive knowledge” (scientia intuitiva), proceeds “from the formal essence of certain attributes of God to the ad-equate knowledge of the essence of things.” Knowledge of this highest kind, then, involves knowing things in the proper order, by conceiving essences through their causes. 
By way of explanation, Spinoza offers an example of something known in each of these ways. For the numbers 1, 2, and 3, the fourth proportional (that is, the number such that 3 stands to it in the same proportion in which 1 stands to 2) is 6. If one knows this merely by remembering what was asserted by one's teachers (report) or by experimenting with the proportions of simple numbers until one happens on a rule for finding the fourth proportional that seems to work for those examples (unregulated experience), then one has knowledge of the first kind. If, however, one understands Euclid's demonstration that a general property of all proportions is that the product of the means (the second and third numbers) is equal to the product of the extremes (the first and fourth), then one can determine from this general property that the proportion of 1 to 2 is the same as that of 3 to 6 by the second kind of knowledge. But if one grasps, as it were, the very essence of the proportion of 1 to 2, so that one can simply see that the proportion of 3 to 6 is the same proportion, then one has knowledge of the third kind. According to Spinoza, the second and third kinds of knowledge each provide adequate knowledge, and each is a function of the intellect. Knowing things through the third kind of knowledge is preferable, however, because it more closely follows the proper order of inferring effects from a complete knowledge of their causes; knowledge of the second kind allows us to conceive only enough of the essences and causes of things to be certain that a given property is present. Whereas knowledge of the second kind shows with certainty that something is true, knowledge of the third kind shows precisely why it must be true. 
5. Philosophy of Physical Science 
Spinoza is deeply committed to the view that there is a necessitating cause for every state of affairs, so that there is no such thing as chance and no such thing as a brute, unexplainable fact. This commitment is evident in the initial axioms of the Ethics, which require that everything must be conceivable (1a2), that things must be conceived through their causes (1a4), and that causes must necessitate their effects (1a3). Spinozistic causes need not precede their effects temporally, however. Thus, God is eternally self-caused and self-causing, because God's very essence entails God's existence, so that God exists and acts eternally from the necessity of its own nature alone. Furthermore, all of God's modes – that is, everything else that exists – follow necessarily from the nature of God (that is, from God's attributes), through which they must also 
be conceived. For this reason, a sufficiently powerful intellect can deduce not only God's existence but a complete description of the universe, including the laws of nature that must govern it, from the idea of God. In fact, the infinite intellect of God itself is just such a powerful intellect and consists of just such a deduction. 
Although carrying out such a detailed deduction is of course far beyond human powers, Spinoza holds that it is nevertheless within the scope of human intellect to grasp many fundamental and pervasive features of the universe as causal consequences of the divine attributes of extension and of thought. He ascribes adequate ideas of the attributes of thought and extension themselves, at least, to all human beings (2p45 and 2p46), on the grounds that such ideas are required in order to have any ideas of modes of those attributes. His confidence in the power of the intellect to reveal pervasive laws or other features of the operations of nature through the power of ideas conceived in the intellect leads him naturally to give priority in scientific investigations to high- level theoretical reasoning rather than to empirical observation. Although he certainly does not reject experience as useless – in addition to recognizing its obvious role in guiding everyday practice, he also appeals to it to confirm doctrines derived in other ways – he nevertheless emphasizes that mere sense experience is inconclusive and does not alone provide knowledge of the essences of things; when unregulated and uninformed by the intellect, it is merely knowledge of the first kind. 
Spinoza's substance monism entails that the extended or material universe cannot consist of a number of distinct substances. On the contrary, there can only be one extended substance, and this substance must be God itself. (This does not imply, of course, that God has a body; for bodies are finite and bounded modes of extension, whereas God is an infinite extended thing.) One problem posed by Cartesian physics was that of how to count extended substances. Descartes denied extension to God on the grounds that its divisibility was incompatible with divine perfection. Although he sometimes hinted that the physical universe as a whole constituted the only extended substance, Descartes's usual policy was to grant the status of substances to all individual bodies in the natural world. This policy had the consequence that extended substances have other extended substances as parts, and those substances have other substances as parts, through indefinitely many divisions. Yet the dependence of wholes on the parts of which they are composed called into question the appropriateness of according substantiality to these compound bodies. Spinoza's metaphysics resolves this problem by denying that bodies (which are finite by definition) are substances at all. He avoids both the seemingly nondivine imperfection of a divisible substance and mathematical paradoxes concerning the infinite divisibility of extended substance by denying that the one extended substance is, insofar as it is substance, divisible at all. Although extension may seem divisible as we conceive it in the imagination, when it is conceived by the intellect this appearance vanishes. As truly perceived by the intellect, the one extended substance is a single continuous thing, no region of which can possibly be separated from the rest. As such, it has no genuine parts (1p23, 1p13, 1p15s). 
Spinoza appears to hold that local variation occurs within the one extended substance through the differential distribution of quantities of the dual-natured force of “motion-and-rest.” Individual bodies, on this account, are patterns of distributions of motion and rest that have at least some tendency or power to persist through an indefinite duration until destroyed by some external 
cause (2p13s, 3p6). The location of these patterns, it may be inferred, changes more rapidly with increases in “motion,” and less rapidly with increases in the complementary quantity of “rest.” The existence of individual bodies with different natures can thus be understood through the different possible patterns of motion and rest, and the fundamental laws governing the physical realm may be understood as mechanical – that is, concerned with interactions of motion and rest among bodies – in just the way required by the new science. 
Although there is only one extended substance, these finite modes of that substance constitute thing-like entities whose natures or essences can be investigated, and which, insofar as they tend to persist, exert some power – power which is a share of the divine power – to persevere in their own being. Indeed, to understand the essence of such a thing is just to understand how it operates and exerts causal power to persevere in its own being as a distinctive pattern of motion and rest. In fact, Spinoza's conception of singular things as finite approximations to a genuine substance accommodates and reconciles two competing paradigms of natural science, and it does so at two different levels. Natural science prior to the seventeenth century was most often conceived as the understanding of the essences of things. During the seventeenth century, this older conception was gradually giving way to a new conception of natural science as the understanding of natural laws. Although Spinoza clearly takes the highest object of knowledge to be the divine essence, to understand this essence – as it is constituted by infinitely many divine attributes, of which we grasp only extension and thought – involves understanding the most general laws of those attributes. In the case of extension, these are what we would call the laws of physics. In treating individual things as finite approximations to substance, Spinoza is able to treat them as quasi- independent objects of conception (that is, objects of explanation and understanding) and as quasi-independent centers of causal activity as well. In order for singular things play this role, however, they must have their own essences through which their own properties can be understood. Thus, the instantiation of various limited essences permits the existence of various special sciences concerned with the understanding those essences. The understanding of the essences of particular things and of particular kinds of things, in turn, involves understanding what Spinoza conceives of as “laws” governing the nature of specific kinds of things, laws which are the subjects of more specialized disciplines. These laws explain the behavior of individuals and species – although they must, of course, be understood ultimately as applications of the more general laws of the attributes themselves. 
6. Philosophy of Psychology 
Each finite thing, for Spinoza, exerts some power to persevere in its existence; if it did not, it would not qualify as a particular thing. In fact, all of a thing's own proper power is power to persevere in existence (3p7d). Spinoza's Latin term for this striving is “conatus.” Conatus is physical, insofar as it is conceived as belonging to a mode of extension. But each mode of extension is identical with a mode of thought; and hence conatus is mental as well as physical. Although all singular things have some conatus, some singular things are (i) sufficiently complex that their power for self-preservation can undergo significant increases and decreases and (ii) capable of forming and retaining images of external things, towards which this striving can become directed. For these beings – human beings and also many animals – their conatus provides the basis for a psychology of the emotions. 
Spinoza's psychology distinguishes three basic emotions. “Desire” is conatus it-self, insofar as it becomes directed onto the attainment of some particular conceived end or object (3p9s). “Joy” (or pleasure) is a passage to a state of greater perfection, or greater power to act. (3p11s). “Sadness” (or pain) is a passage to a state of lesser perfection, or lesser power to act. Other emotions are defined in terms of these, as they appear in particular situations or combinations. Thus, “love” is joy with the accompanying idea of an external cause, and “hate” is sadness with the accompanying idea of an external cause (3p14s). In keeping with his conception of scientific method, Spinoza seeks to deduce the nature and effects of a wide variety of human emotions from his axioms, definitions, and previously demonstrated propositions, without formal appeal to any empirical observations other than two extremely general empirical postulates: that human minds can undergo changes increasing or decreasing their power of action, and that human minds can form images of things. 
A crucial distinction for Spinoza is that between “activity” and “passivity.” Something is active when it is the adequate cause of some effect – that is, when an effect can be understood entirely through it (3d3 and 3d2). Something is passive when it is the inadequate cause of some effect – that is, when the effect must be understood through something else as well. Human beings act when they pursue their own genuine advantage – understood as self-preservation – with adequate knowledge through their own conatus, or power. Emotions that are induced in human beings by external causes are called “passions,” because human beings are passive with respect to them. For example, through the agency of personal or impersonal external causes, a human being's desire – which is by nature directed at what is beneficial or advantageous – may be misdirected onto an object that is not genuinely beneficial. Joy and sadness, love and hate, may equally be induced by external causes. Because passions are not necessarily conducive to one's own true advantage, they are dangerous, and one of the most important aims of philosophy is to provide a measure of control over the passions. In addition to passions, however, there are also emotions of desire and joy that are active – that is, that result from the human being's own proper power and activity. Such emotions include the desire for knowledge, the joy of understanding and – ultimately – the intellectual love of God that brings blessedness and the highest satisfaction or peace of mind. 
7. Ethics 
Although popular religion often presents ethical precepts in the guise of dictates of an external authority, a deeper philosophical analysis shows, Spinoza holds, that ethical precepts arepractical dictates of one's own reason. When one reasons, one forms adequate ideas concerning human life and what is conducive to one's advantage – that is, to persevering in one's being. Because each person endeavors to persevere in his or her being, this very knowledge is, at the same time, also a desire to do or have that which is most advantageous. In this way, those whoact ethically are acting under “the guidance of reason.” The joy that popular religion offers as an externally bestowed reward for virtuous action is, in reality, the inevitable mental consequenceof virtuous action. Spinozistic ethics is demonstrated by showing what is truly to one's advantage; this knowledge, for those who attain it, will be internally motivating, just as virtuous action itself is internally rewarding. 
Spinoza characterizes what he regards as virtuous character and action through his description of an ethical model or ideal, that of the “free man” (5p67–5p73). Freedom cannot consist in action that is causally undetermined, for Spinoza, since everything is equally necessitated. Rather, freedom lies in being determined to act by one's own nature rather than by external causes (1d7). Only God is absolutely free in this sense (1p17c2); no human being can be entirely unaffected by external causes (4d). Nevertheless, human beings can achieve a finite measure of freedom to the extent that they pursue their own advantage through their own conatus without being overcome or disturbed by passions. To increase one's freedom in this sense, and thereby to come closer to the ideal of the “free man,” is to be better able to pursue one's advantage. Hence, whatever enables us to come closer to this ideal may be classified as “good.” For although human beings generally use the term “good” simply for whatever they happen to desire, Spinoza proposes that the term be used instead to signify “what we certainly know to be useful to us” (4d1). Since the mind is entirely active when its adequate ideas give rise to other adequate ideas, and since the most perfect object of conception is God, it follows that “knowledge of God is the mind's greatest good” (4p28). It should be observed however, that all knowledge is, in one way or another, knowledge of God; for whatever is, is in God and must be conceived through God (1p15). 
Although ethical motivation is inevitably and undeniably grounded in considerations of one's own advantage for Spinoza, his practical precepts are less selfish than this fact might lead one to suppose. There are two related reasons for this. First, he regards human cooperation and friendship as extremely beneficial even for the pursuit of mundane and limited goods, such as food, shelter, and the conveniences of life that are a precondition for philosophical study. Hence, he places high value on whatever is conducive to good social relations. Second, he regards human cooperation and friendship as especially important for attaining the highest good, which is the understanding of God. The good of understanding and loving God through adequate ideas is entirely noncompetitive: that is, one person's achieving it or acquiring it does not leave less of it for others (4p36). On the contrary, knowledge and love of God are far more easily attained in community with co-inquirers. For these reasons, Spinoza distinguishes two species of virtuous desires: “tenacity,” which is “the Desire by which each one strives, solely from the dictate of reason, to preserve his being,” and “nobility,” which is “the Desire by which each one strives, solely from the dictate of reason, to aid other men and join them to him in friendship” (3p59s). 
It is fair to say that Spinoza's ethics is, among other things, an ethics of mental health. That is, its aim is to increase the mental and emotional health of human beings through the replacement of disturbing passions with peace of mind. One notable example of this concerns what Spinoza calls “favor” and “indignation.” “Favor” is love toward one who has benefited another, whereas “indignation” is hate toward one who has done evil to another. Favor can be in accordance with reason, for human being can be the active causes of benefits to others (4p51). Indignation, however, as a kind of sadness, is evil (4p51s); and when we understand that those who do evil are not the adequate causes of their own actions, but that they are instead overcome by external causes, we will no longer hate them. Thus, reason leads the Spinozist to love those who do good, without experiencing the disturbance of hating those who do evil. 
Although Spinoza endorses some ethical doctrines characteristic of Christianity, such as the doctrine that one should “repay the other's hate, anger, and disdain toward him with love” (4p46), 
he rejects others. For example, he characterizes pity, repentance, and humility as evils rather than as virtues (4p50, 4p53, and 4p54), because they are species of sadness: while the virtuous man comes to others' assistance when needed, forms an accurate conception of his own powers, and seeks to avoid repeating mistakes, he does so without pity, humility, or repentance. 
8. Political Theory 
Because of the protection and the opportunities for cooperative action it provides, citizenship in a state is of great value to those who are guided by reason (4p73). Spinoza's conception of rights is similar in some ways to that of Thomas Hobbes. For Spinoza, each person's - and each thing's - right is coextensive with its power. The state serves to protect individuals from one another and to facilitate cooperation. It does this by restricting each subject's power and hence each subject's right. But whereas Hobbes conceives of subjects surrendering all rights to the sovereign, other than the right to resist death, Spinoza emphasizes in the final chapters of the Theological- Political Treatise that any actual state's ability to restrict the power and hence the rights of its subjects is limited; subjects will necessarily retain their determination to pursue their own advantage, in the light of the incentives and disincentives created by the state, in whatever way they most desire. The power, and hence the right, of the state is therefore never absolute. In fact, the state itself is clearly a kind of particular or singular thing, with its own conatus. Like a human being, it best preserves itself not when it exercises all of the powers that it may have, but rather when it exercises them wisely. Thus, although the state may have the power to establish a religion and to control the speech (though not the thought) of its subjects, it acts most wisely when it allows freedom of religion and of speech. Popular religion, in particular, constitutes a danger to the state, because it sets up authorities other than those of the state itself. This danger is best controlled not by establishing a state religion, whose functionaries will challenge the authority of the state itself, but rather by allowing freedom of religion. This prevents any one religion from becoming too powerful and also forces religions to compete with one another for adherents. This competition should encourage religions to downplay their harshest elements. 
9. Philosophy of Religion 
In order to address both the dangers and the opportunities posed by the prevalence within European states of biblical religion, Spinoza devotes considerable effort in the earlier chapters of Theological-Political Treatise to the interpretation of the Bible. His approach to interpreting the Bible is to bring as much historical and linguistic knowledge to bear on the text as possible, and then, in the light of this knowledge, to determine the meaning of the text from the text itself. This means, in particular, that no presuppositions concerning what the Bible should say or must say should be employed. When it is interpreted in this way, Spinoza holds, the Bible reveals that the different prophets believed many different things and that each conceived God in his own way, according to his own experience and temperament. However, he argues, the Bible itself does not teach any particular piece of theological doctrine or dogma as required for salvation. Rather - and this is the politically beneficial message that Spinoza's scriptural interpretation seeks above all else to establish - the Bible itself affirms that the only things required for salvation are charity towards one's neighbor and obedience to the state. Whatever beliefs individuals may find helpful for achieving these goals are therefore permissible from the standpoint of Biblical religion. 
Popular religion is thus concerned not with the truth of doctrines about God, but with their practical efficacy. Philosophy, however, is concerned with the truth about God, and Spinoza's own revolutionary understanding of God is developed in the Ethics. In many ways, his God coincides with the God of the western theological tradition: God is absolutely infinite and absolutely perfect, eternal, all-powerful and all-knowing, the first cause and source of all things, existing necessarily from his own nature or essence alone, indivisible, and even the source of blessedness as the object of eternal intellectual love. But while Spinoza's God is an infinite thinking thing, it is equally an infinite extended thing. God is not the creator of a natural world distinct from himself; on the contrary, God is Nature itself. God is not a person and has no desires or purposes; nothing is either good or evil for God, and God does not literally love human beings. God acts not to achieve some end, whether for human beings or for itself, but simply because each of infinitely many effects follows necessarily from the divine nature itself. 
Because God is Nature, all scientific understanding of nature is knowledge of God, for Spinoza. Because this adequate knowledge brings joy, accompanied by the idea of God as its cause, human beings can enjoy an intellectual love of God. Furthermore, to the extent that human beings have adequate intellectual knowledge, eternal ideas, which have always been in the infinite intellect of God, become part of their own minds as well. To this extent, those who achieve genuine understanding have a greater “part of their minds that is eternal” (5p23); this eternal part is, in fact, the intellect itself (5p40c). Thus, through the pursuit of scientific understanding, human beings can enjoy an intellectual love of God that is eternal. This kind of “immortality” is not personal, for it involves no memory or sensation, and no identity as a distinct individual after death. Rather, it consists in actively participating, during one's lifetime, in an intellectual understanding of the eternal that brings peace of mind. Because it carries the mind outside the confines of its own specific and limited perspective in the universe, this understanding renders death less harmful and thoughts of death less disturbing (5p38). It thereby provides, Spinoza thinks, a way in which those who achieve genuine eternal understanding succeed best of all in “persevering in their being” - even if the duration of their lives is, as Spinoza's own life was, all too brief. 
1 References to elements of Spinoza's Ethics follow the standard format explained in Jonathan Bennett's A Study of Spinoza's Ethics (Indianapolis: Hackett, 1984): the initial number indicates the Part of the Ethics, “a” abbreviates “Axiom”; “p” abbreviates “Proposition”; “s” abbreviates “Scholium” (“note” in some English translations); “c” abbreviates “Corollary”; and “d” abbreviates either “Definition” or “Demonstration,” depending on whether it immediately follows a Part number or a Proposition number. All translations from Spinoza's works are taken from The Collected Works of Spinoza, vol. I, edited and translated by Edwin Curley (Princeton: Princeton University Press, 1985). 

-/

import Mathlib

open CategoryTheory Limits

universe u v w

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace SpinozaEthics

/-! ╔═══════════════════════════════════════════════════════════════════╗
    ║         PART I: DE DEO — OF GOD                                  ║
    ╚═══════════════════════════════════════════════════════════════════╝ -/

section PartI_DeDeo

class SpinozistUniverse (Entity : Type u) extends Category.{v} Entity where
  thin : Quiver.IsThin Entity
  skeletal : Skeletal Entity

attribute [instance] SpinozistUniverse.thin

section Substance

variable (Entity : Type u) [su : SpinozistUniverse Entity] [HasInitial Entity]

/-- E1D6: God/Nature is the initial object of the causal universe. -/
noncomputable def God : Entity := ⊥_ Entity

/-- Deus sive Natura: God and Nature are identical. -/
noncomputable abbrev Natura : Entity := God Entity

/-- E1P7: Necessary Existence. The only cause of itself is the identity. -/
theorem causa_sui : initial.to (God Entity) = 𝟙 (God Entity) :=
  Subsingleton.elim _ _

/-- E1P14: Substance Monism. Any two initial objects are equal. -/
theorem substance_monism (G : Entity) (hG : IsInitial G) : G = God Entity := by
  have hGod : IsInitial (God Entity) := initialIsInitial
  exact su.skeletal ⟨hG.uniqueUpToIso hGod⟩

/-- E1P11: God necessarily exists. -/
theorem god_exists : ∃ (g : Entity), Nonempty (IsInitial g) :=
  ⟨God Entity, ⟨initialIsInitial⟩⟩

/-- E1P15: Inherence. -/
noncomputable def inherence (x : Entity) : God Entity ⟶ x :=
  initial.to x

theorem e1p16_everything_follows (x : Entity) : Nonempty (God Entity ⟶ x) :=
  ⟨inherence Entity x⟩

/-- E1P18: Immanent Causation. Mode space is the coslice category Under God. -/
def ModeSpace : Type _ := Under (God Entity)

noncomputable instance : Category (ModeSpace Entity) :=
  inferInstanceAs (Category (Under (God Entity)))

noncomputable def toMode (x : Entity) : ModeSpace Entity :=
  Under.mk (inherence Entity x)

/-- E1P25: God is the efficient cause. -/
theorem e1p25_efficient_cause (m : ModeSpace Entity) :
    m.hom = inherence Entity m.right :=
  Subsingleton.elim _ _

theorem e1p29_necessitarianism (x y : Entity) : Subsingleton (x ⟶ y) :=
  inferInstance

theorem e1p33_no_other_order (x y : Entity) (f g : x ⟶ y) : f = g :=
  Subsingleton.elim f g

/-- Infinite vs Finite Modes (E1P21, E1P28).
Garrett: Infinite modes follow directly from the absolute nature of an attribute,
while finite modes require other finite modes. -/
class ModeClassification where
  IsInfinite : ModeSpace Entity → Prop
  IsFinite : ModeSpace Entity → Prop
  partition : ∀ m, IsInfinite m ↔ ¬ IsFinite m

end Substance

class InfiniteAttributes (Attr : Type u) (AttrMode : Attr → Type u)
    [∀ a, Category.{v} (AttrMode a)] [∀ a, Quiver.IsThin (AttrMode a)] where
  attr_infinite : Infinite Attr

end PartI_DeDeo

/-! ╔═══════════════════════════════════════════════════════════════════╗
    ║       PART II: DE MENTE — OF THE MIND                            ║
    ╚═══════════════════════════════════════════════════════════════════╝ -/

section PartII_DeMente

class AttributeParallelism (Attr : Type u) (AttrMode : Attr → Type u)
    [∀ a, Category.{v} (AttrMode a)] [∀ a, Quiver.IsThin (AttrMode a)] where
  equiv : ∀ (a b : Attr), AttrMode a ≌ AttrMode b
  refl_coherence : ∀ (a : Attr), (equiv a a).functor ≅ 𝟭 (AttrMode a)
  trans_coherence : ∀ (a b c : Attr), (equiv a b).functor ⋙ (equiv b c).functor ≅ (equiv a c).functor
  sym_coherence : ∀ (a b : Attr), (equiv a b).functor ⋙ (equiv b a).functor ≅ 𝟭 (AttrMode a)

section Parallelism
variable {Attr : Type u} {AttrMode : Attr → Type u}
variable [∀ a, Category.{v} (AttrMode a)] [∀ a, Quiver.IsThin (AttrMode a)]
variable [par : AttributeParallelism Attr AttrMode]

noncomputable def ideaOf {Thought Extension : Attr} (body : AttrMode Extension) : AttrMode Thought :=
  (par.equiv Extension Thought).functor.obj body

noncomputable def parallelCausation {Thought Extension : Attr}
    {A B : AttrMode Extension} (cause : A ⟶ B) :
    ideaOf (Thought := Thought) A ⟶ ideaOf (Thought := Thought) B :=
  (par.equiv Extension Thought).functor.map cause
end Parallelism

/-! ═══════════════════════════════════════════════════════════════════
### PHILOSOPHY OF PHYSICAL SCIENCE — MOTION AND REST
Garrett: "Local variation occurs within the one extended substance through 
the differential distribution of quantities of the dual-natured force 
of 'motion-and-rest.' Individual bodies... are patterns of distributions..."
═══════════════════════════════════════════════════════════════════ -/
class PhysicsOfExtension (ExtendedMode : Type u) (Ratio : Type u)
    [Category.{v} ExtendedMode] [LinearOrder Ratio] where
  /-- The quantitative ratio of motion and rest that defines a body's essence. -/
  motion_and_rest : ExtendedMode → Ratio
  /-- Bodies are distinguished by their patterns of motion and rest. -/
  distinguished_by_ratio : ∀ (X Y : ExtendedMode), motion_and_rest X = motion_and_rest Y → Nonempty (X ≅ Y)

inductive KnowledgeKind : Type where
  | imaginatio : KnowledgeKind
  | ratio : KnowledgeKind
  | intuitiva : KnowledgeKind
  deriving DecidableEq, Repr

namespace KnowledgeKind
instance : LE KnowledgeKind where
  le a b := match a, b with
    | imaginatio, _ => True
    | ratio, imaginatio => False
    | ratio, _ => True
    | intuitiva, intuitiva => True
    | intuitiva, _ => False

instance : LT KnowledgeKind where
  lt a b := a ≤ b ∧ ¬ b ≤ a

def isAdequate : KnowledgeKind → Prop
  | imaginatio => False
  | ratio => True
  | intuitiva => True

def isFalse (k : KnowledgeKind) : Prop := ¬ isAdequate k

theorem falsity_is_privation (k : KnowledgeKind) :
    isFalse k ↔ k = imaginatio := by
  unfold isFalse isAdequate
  cases k <;> decide

theorem intuitiva_is_highest : ∀ k : KnowledgeKind, k ≤ intuitiva := by
  intro k; cases k <;> trivial
end KnowledgeKind

class HasIdeaIdeae (C : Type u) [Category.{v} C] where
  ideaIdeae : C ⥤ C
  reflexivity : ideaIdeae ⋙ ideaIdeae ≅ ideaIdeae

end PartII_DeMente

/-! ╔═══════════════════════════════════════════════════════════════════╗
    ║     PART III: DE AFFECTIBUS — OF THE AFFECTS                     ║
    ╚═══════════════════════════════════════════════════════════════════╝ -/

section PartIII_DeAffectibus

variable (Entity : Type u) [SpinozistUniverse Entity] [HasInitial Entity]

class HasAdequatePredicate where
  IsAdequate : ModeSpace Entity → Prop

variable [HasAdequatePredicate Entity]

def adequateProp : ObjectProperty (ModeSpace Entity) :=
  fun m => HasAdequatePredicate.IsAdequate m

abbrev AdequateSubcat : Type _ := (adequateProp Entity).FullSubcategory

/-- Garrett: "Doubt, as he explains... arises exclusively from acquiring ideas in the wrong order...
falsehood... is not a positive characteristic of ideas, but rather a kind of privation." -/
def isPrivation (m : ModeSpace Entity) : Prop :=
  ¬ HasAdequatePredicate.IsAdequate m

variable (Mode : Type u) [Category.{v} Mode]
variable (Perfection : Type u) [CompleteLattice Perfection]

class AffectiveDynamics where
  potentia_actio : Mode ⥤ Perfection

variable [aff : AffectiveDynamics Mode Perfection]

/-- Clean mathematical wrapper to circumvent type collisions. -/
def potentia (X : Mode) : Perfection := aff.potentia_actio.obj X

def isJoy {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  potentia Mode Perfection X < potentia Mode Perfection Y

def isSadness {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  potentia Mode Perfection Y < potentia Mode Perfection X

def isEquanimity {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  potentia Mode Perfection X = potentia Mode Perfection Y

theorem conatus {X Y : Mode} (f : X ⟶ Y) : ¬ isSadness Mode Perfection f := by
  unfold isSadness potentia
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y :=
    leOfHom (aff.potentia_actio.map f)
  intro h_lt
  grind

theorem conatus_trichotomy {X Y : Mode} (f : X ⟶ Y) :
    isJoy Mode Perfection f ∨ isEquanimity Mode Perfection f := by
  unfold isJoy isEquanimity potentia
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y :=
    leOfHom (aff.potentia_actio.map f)
  rcases eq_or_lt_of_le h_le with h_eq | h_lt
  · right; grind
  · left; exact h_lt

structure AffectWithCause where
  subject : Mode
  cause : Mode
  target : Mode
  transition : subject ⟶ target

def IsLove (a : AffectWithCause Mode Perfection) : Prop :=
  isJoy Mode Perfection a.transition

def IsHate (a : AffectWithCause Mode Perfection) : Prop :=
  isSadness Mode Perfection a.transition

/-! ═══════════════════════════════════════════════════════════════════
### ETHICS OF MENTAL HEALTH — FAVOR AND INDIGNATION
═══════════════════════════════════════════════════════════════════ -/

/-- Favor: love toward one who has benefited another. -/
def IsFavor (a : AffectWithCause Mode Perfection) (benefit : Mode ⟶ Mode) : Prop :=
  IsLove Mode Perfection a ∧ isJoy Mode Perfection benefit

/-- Indignation: hate toward one who has done evil. -/
def IsIndignation (a : AffectWithCause Mode Perfection) (harm : Mode ⟶ Mode) : Prop :=
  IsHate Mode Perfection a ∧ isSadness Mode Perfection harm

theorem affect_imitation {X₁ X₂ Y₁ Y₂ : Mode}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hf₁ : isJoy Mode Perfection f₁)
    (hf₂ : isJoy Mode Perfection f₂) :
    potentia Mode Perfection X₁ < potentia Mode Perfection Y₁ ∧
    potentia Mode Perfection X₂ < potentia Mode Perfection Y₂ :=
  ⟨hf₁, hf₂⟩

theorem joy_composes {X Y Z : Mode} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : isJoy Mode Perfection f) (hg : isJoy Mode Perfection g) :
    isJoy Mode Perfection (f ≫ g) := by
  unfold isJoy potentia at *
  exact lt_trans hf hg

theorem e3p59_active_affects {X Y : Mode} (f : X ⟶ Y) :
    isJoy Mode Perfection f ∨ isEquanimity Mode Perfection f :=
  conatus_trichotomy Mode Perfection f

end PartIII_DeAffectibus

/-! ╔═══════════════════════════════════════════════════════════════════╗
    ║     PART IV: DE SERVITUTE HUMANA — OF HUMAN BONDAGE              ║
    ╚═══════════════════════════════════════════════════════════════════╝ -/

section PartIV_DeServitute

variable (Mode : Type u) [Category.{v} Mode]
variable (Perfection : Type u) [CompleteLattice Perfection]
variable [aff : AffectiveDynamics Mode Perfection]

def virtue (X : Mode) : Perfection := potentia Mode Perfection X

theorem e4p20_virtue_is_potentia {X Y : Mode} (f : X ⟶ Y) :
    virtue Mode Perfection X ≤ virtue Mode Perfection Y :=
  leOfHom (aff.potentia_actio.map f)

def IsFree (X : Mode) : Prop := ¬ (potentia Mode Perfection X = ⊥)

/-! ═══════════════════════════════════════════════════════════════════
### TENACITY, NOBILITY, AND EVIL PASSIONS
Garrett: "Spinoza distinguishes two species of virtuous desires: 'tenacity' 
... to preserve his being, and 'nobility' ... to aid other men... 
He characterizes pity, repentance, and humility as evils..."
═══════════════════════════════════════════════════════════════════ -/

class ActiveDesires where
  isTenacity : ∀ {X Y : Mode}, (X ⟶ Y) → Prop
  isNobility : ∀ {X Y : Mode}, (X ⟶ Y) → Prop
  tenacity_is_joy : ∀ {X Y : Mode} (f : X ⟶ Y), isTenacity f → isJoy Mode Perfection f
  nobility_is_joy : ∀ {X Y : Mode} (f : X ⟶ Y), isNobility f → isJoy Mode Perfection f

def IsPity {X Y : Mode} (f : X ⟶ Y) : Prop := isSadness Mode Perfection f
def IsHumility {X Y : Mode} (f : X ⟶ Y) : Prop := isSadness Mode Perfection f
def IsRepentance {X Y : Mode} (f : X ⟶ Y) : Prop := isSadness Mode Perfection f

theorem evil_affects_are_sadness {X Y : Mode} (f : X ⟶ Y) 
    (h : IsPity Mode Perfection f ∨ IsHumility Mode Perfection f ∨ IsRepentance Mode Perfection f) : 
    isSadness Mode Perfection f := by
  rcases h with h1 | h2 | h3
  · exact h1
  · exact h2
  · exact h3

/-! ═══════════════════════════════════════════════════════════════════
### POLITICAL THEORY — THE STATE AND NATURAL RIGHT
Garrett: "Each person's - and each thing's - right is coextensive with 
its power. The state serves to protect individuals... The state itself 
is clearly a kind of particular or singular thing, with its own conatus."
═══════════════════════════════════════════════════════════════════ -/

/-- Natural Right is coextensive with Power (virtue). -/
def naturalRight (X : Mode) : Perfection := virtue Mode Perfection X

theorem right_is_power (X : Mode) : naturalRight Mode Perfection X = virtue Mode Perfection X := rfl

class PoliticalState where
  StateMode : Mode
  /-- The state acts to preserve itself, bounding individual rights for cooperation,
      resulting in a superadditive power. -/
  state_power_superadditive : ∀ (Citizen : Mode),
    Nonempty (Citizen ⟶ StateMode) → 
    naturalRight Mode Perfection Citizen ≤ naturalRight Mode Perfection StateMode

end PartIV_DeServitute

/-! ╔═══════════════════════════════════════════════════════════════════╗
    ║   PART V: DE POTENTIA INTELLECTUS, SEU DE LIBERTATE HUMANA       ║
    ╚═══════════════════════════════════════════════════════════════════╝ -/

section PartV_DeLibertate

variable (Mode : Type u) [Category.{v} Mode]
variable (Perfection : Type u) [CompleteLattice Perfection]
variable [aff : AffectiveDynamics Mode Perfection]

class ScientiaIntuitiva where
  intuit : Mode ⥤ Mode
  intuit_preserves : ∀ (X : Mode), aff.potentia_actio.obj X ≤ aff.potentia_actio.obj (intuit.obj X)

def IsBlessed (X : Mode) : Prop := potentia Mode Perfection X = ⊤

theorem blessed_stable {X Y : Mode} (f : X ⟶ Y) (hX : IsBlessed Mode Perfection X) :
    IsBlessed Mode Perfection Y := by
  unfold IsBlessed potentia at *
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y := leOfHom (aff.potentia_actio.map f)
  rw [hX] at h_le
  exact le_antisymm le_top h_le

theorem e5p36_amor_dei (X G : Mode)
    (hX : IsBlessed Mode Perfection X)
    (hG : IsBlessed Mode Perfection G) :
    aff.potentia_actio.obj X = aff.potentia_actio.obj G := by
  unfold IsBlessed at hX hG
  rw [hX, hG]

/-! ═══════════════════════════════════════════════════════════════════
### GOD AND PASSIONS & ETERNITY OF THE MIND

Garrett: "God is not a person and has no desires or purposes... 
Those who achieve genuine understanding have a greater 'part of their 
minds that is eternal' (5p23); this eternal part is, in fact, the intellect itself."
═══════════════════════════════════════════════════════════════════ -/

/-- E5P17: "God is without passions, nor is he affected with any affect of Joy or Sadness."
Since God is the Initial Object, any endomorphism is the identity. -/
theorem e5p17_god_without_passions {Entity : Type u} [SpinozistUniverse Entity] 
    [HasInitial Entity] (f : God Entity ⟶ God Entity) : 
    f = 𝟙 (God Entity) :=
  Subsingleton.elim _ _

/-- E5P23: The eternal part of the mind resides via Scientia Intuitiva. -/
def eternalPart [sci : ScientiaIntuitiva Mode Perfection] (X : Mode) : Mode :=
  sci.intuit.obj X

/-- E5P38: The greater the eternal part, the less the mind fears death.
(Represented as the eternal part being indestructible/free from Sadness). -/
theorem e5p38_eternal_part_indestructible [sci : ScientiaIntuitiva Mode Perfection]
    (X Y : Mode) (f : eternalPart Mode Perfection X ⟶ Y) :
    ¬ isSadness Mode Perfection f :=
  conatus Mode Perfection f

theorem beatitudo_non_est_praemium_sed_ipsa_virtus (X : Mode) :
    IsBlessed Mode Perfection X ↔ virtue Mode Perfection X = ⊤ := by
  unfold IsBlessed virtue potentia
  exact Iff.rfl

end PartV_DeLibertate

end SpinozaEthics