# ZFfin-formalization

The axiomatization of the theory of hereditarily finite sets in first-order classical logic is systematically explored and formalized in Isabelle/HOL. An inductive definition of first-order definable predicates is introduced and used to formalize axiom schemata. Special attention is paid to several equivalent axioms of finiteness, as well as to several equivalent ways of expressing regularity. The work also formalizes several facts on independence of an axiom from a system of axioms by defining appropriate models.

## Requirements and usage

The code is compatible with Isabelle2025-2. See [Isabelle web page](https://isabelle.in.tum.de/) for download and installation instructions.

The (short) theory ZFfin_HF.thy depends on the [Archive of Formal Proofs](https://isa-afp.org/) (AFP) session HereditarilyFinite. To use AFP see its [Download](https://isa-afp.org/download/) and [Help](https://isa-afp.org/help/) pages.

For an Isabelle beginner:
  - installing Isabelle is very easy,
  - start Isabelle (the Isabelle/jEdit editor opens), and open one of the repository files from the directory where it was cloned or downloaded,
  - putting a cursor at any place in the theory, the "Output" tab (bottom) and the "State" tab (right) show the current state of the theory verification (Tip: one can also check the "Proof state" box in the "Output" tab for a unified view),
  - the verification is continuous, it takes some time to complete at the start and any time an edit is made; 
    - a pink background or right bar indicates verification is in progress (e.g. ZFfin.thy takes about 30s to finish); 
    - see also the "Theories" tab (right) for the overall verification progress,
  - installing AFP takes a few more steps; it is needed for ZFfin_HF.thy only, which can be skipped with little loss.  

## Content
**ZFfin.thy**
  is the main theory 
- Section _Signature_ introduces membership as a polymorphic binary predicate (i.e. a graph over `'a`) and defines basic notions
   - The subsection _Set relations and properties_ defines set-theoretically-definable predicates. This is crucial for axiom schemata. 
- Section _Axiomatizations of hereditarily finite sets_ contains the hieearchy of locales corresponding to different fragments of the Zermelo-Fraenkel set theory without infinity.
   - For an overview use the _Sidekick_ tab in Isabelle/jEdit editor.
   - Dependencies are mainly proven using `sublocale` command. 
   - The last subsection _Summary of dependences_ highlights some selected facts. 
      - In particular, it introduces two equivalent collections of axioms, **ZFfin** and **AST** (for Alternative Set Theory of Petr Vopěnka), that capture two different axiomatizations of the whole theory of hereditarily finite sets.
   
 **ZFfin_HF.thy** is a (very short) theory verifies that the existing [formalization of hereditarily finite sets by Paulson](https://isa-afp.org/entries/HereditarilyFinite.html), based on the Ackermann encoding, is an instance of ZFfin. The theory depends on AFP.

**Permutation_models.thy** formalizes in full generality the Bernays-Rieger method of construction of nonstandard models. The theory serves as a foundation for two particular models in other theories.

**Not_ts_model.thy** employs the Bernays-Rieger method and formalizes construction of a model that 
- satisfies axioms of extensionality, empty set, powerset, union, regularity, replacement and set induction,
- does not satisfy transitive superset axiom (not all sets have a transitive superset),
- therefore in particular does not satisfy the axiom schema of regularity. 
 
 The permutation in question is $n \leftrightarrow \{n+1\}$, $n \in \omega$.

 **Not_regular_model.thy** employs the Bernays-Rieger method and formalizes construction of a model that 
- satisfies axioms of extensionality, empty set, powerset, union, replacement, set induction and transitive superset,
- does not satisfy regularity.

 The permutation in question is $\emptyset \leftrightarrow \{\emptyset\}$.
