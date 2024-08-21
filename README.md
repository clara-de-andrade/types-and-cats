# Ntes on Types and Categories

These are my study notes on homotopy type theory (HoTT). The main objective, among various others, is to present the elementary portion of HoTT as a formal theory unifying formal logic, set theory, higher category theory and homotopy theory, and to do so in a clear, rigorous and systematic manner, and in a way accessible to mathematics undergraduate students with previous knowledge only of the elementary portions of these disciplines---and also, the notes are written in Brazilian Portuguese, since the [HoTT book](https://homotopytypetheory.org/book/) is freely avaible in English already.

The present text is still a work in progress, and it and its source code are both subject to change without prior notice. Currently, the repository is meant to be viewed on an IDE for Coq such as VSCode with the VSCoq extension, and the proofs depend on the `coq-hott` package for the HoTT library replacing `Coq.Init.Prelude`. I'm also assuming you have the prerequired command-line tools to interact with the repository, such as `make`, to readily compile the code and its documentation, and `opam`, to manage dependencies and the Coq installation itself. Finally, the proofs are mostly undocumented and rather basic. There is not much to expect out of this project at the moment.

## TODOs

- [ ] write the documentation in LaTeX, with informal proofs of some theorems
- [ ] introduce the notation of formal proofs in Coq (mainly, tactics)
- [ ] streamline the order of presentation of the main topics
<!--
  primitives -> paths
             -> equivalences
             -> univalence 
             -> propositions, sets, higher grupoids, homotopy types
             -> logic, set theory, higher category theory, homotopy theory
--->
- [ ] write an appendix on how to install Coq and view the repository on an IDE (VS Code, preferably)
- [ ] translate the notes to English

- to learn about Coq:
  + [ ] scopes
  + [ ] tactics