# coqlang_temporal_logic
Formalization of temporal logic in Coq

```
A temporal model for a set of atomic propositions PROP is a triple M=⟨T ≺,V⟩, where ⟨T,≺⟩ is a temporal frame and V is a valuation assigning to every p ∈ PROP a set of time instants V(p)⊆T at which p is declared true.

Equivalently, an interpretation of PROP in T is a mapping I : T × PROP → {true, false} which assigns a truth value to each atomic proposition at each time instant in the temporal frame. The truth of a formula of TL at a given time instant t in a given temporal model M is defined inductively as follows:

M=⟨T,≺,V⟩
M,t ⊨ p iff t∈V(p), for p ∈ PROP;
M,t ⊨ ¬ψ iff it is not the case that M,t⊨ψ;
M,t ⊨ φ ∧ ψ iff M,t ⊨ φ and M,t ⊨ ψ;
M,t ⊨ φ ∨ ψ iff M,t ⊨ φ or M,t ⊨ ψ;
M,t ⊨ Gφ iff M,t'⊨φ for all time instants t' such that t≺t';
M,t ⊨ Xφ iff M,succ(t) ⊨ φ;
M,t ⊨ Fϕ iff M,h,t′⊨ϕ for some t' ∈ h such that t≺t'.
```

*From Stanford encyclopedia of philosophy Temporal Logic article.*

## References

* [Stanford Encyclopedia of Philosophy - Temporal Logic](https://plato.stanford.edu/entries/logic-temporal/#PriBasTenLogTL)
* [Coq Tactics Index](https://pjreddie.com/coq-tactics/)