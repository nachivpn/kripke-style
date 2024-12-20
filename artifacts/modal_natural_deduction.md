# Modal Natural Deduction

A small overview on how natural deduction systems can be used as proof systems for normal modal logics.

## Motivation 

Recall the necessitation rule in axiomatic derivation systems such as in Hilbert-type derivation systems:
```
    A
---------NEC
   □ A

```
In natural deduction systems such an inference rule is no longer sound since in the semantics necessitation only holds at the model level (in contrast to a particular world): 
`M ⊩ A ⇒ M ⊩ □ A`

In this (small) presentation I will explore some ways on how necessitation can be expressed in Fitch-style natural deduction systems.
See [notes](modal_natural_deduction_notes.pdf).

## References

1. Borghuis, VAJ 1994, 'Coming to terms with modal logic: on the interpretation of modalities in typed lambda-calculus', Doctor of Philosophy, Mathematics and Computer Science, Eindhoven. https://doi.org/10.6100/IR427575
