Require Import ZArith.

(* A temporal frame T=⟨T,≺⟩ defines the flow of time over 
which the meanings of the tense operators are to be defined.
Note that, so far, no conditions like transitivity or irreflexivity on the "precedence"relation ≺ are imposed.*)
Parameter TemporalFrame: Set.

(* Logic of the future *)
Inductive LTTerm :=
| Atom: TemporalFrame -> LTTerm
| And: LTTerm -> LTTerm -> LTTerm
| Not: LTTerm -> LTTerm
| Globally: LTTerm -> LTTerm
| Future: LTTerm -> LTTerm
| Next: LTTerm -> LTTerm.

Definition Or a b := Not(And(Not a)(Not b)).
Definition Impl a b := Or (Not a) (b).
Definition Equiv a b := And (Impl a b) (Impl b a).


(*
  Hence □ and ◇ form a dual pair of operators.
  ◇p (future p) is equivalent to ¬□¬p ("not always not-p")
*)
(*Definition Future p := Not (Globally (Not p)).*)

(*
A temporal model for a set of atomic propositions PROP is a triple M=⟨T,≺,V⟩,
where ⟨T,≺⟩ is a temporal frame and V is a valuation assigning to every p∈PROP a set of time instants
V(p)⊆T at which p is declared true.

Equivalently, an interpretation of PROP in T is a mapping I : T × PROP → {true, false}
which assigns a truth value to each atomic proposition at each time instant in the temporal frame.
The truth of a formula of TL at a given time instant t
in a given temporal model M is defined inductively as follows:
M=⟨T,≺,V⟩
M,t ⊨p iff t∈V(p), for p ∈ PROP;
M,t ⊨¬ψ iff it is not the case that M,t⊨ψ;
M,t ⊨φ ∧ ψ iff M,t ⊨ φ and M,t ⊨ ψ;
M,t ⊨φ ∨ ψ iff M,t ⊨ φ or M,t ⊨ ψ;
M,t ⊨Gφ iff M,t'⊨φ for all time instants t' such that t≺t';
M,t ⊨Xφ iff M,succ(t) ⊨ φ;
M,t ⊨Fϕ iff M,h,t′⊨ϕ for some t' ∈ h such that t≺t'.
*)

Fixpoint eval (F :LTTerm) (t :nat) (valuation : TemporalFrame -> Prop) {struct F} : Prop :=
match F with
| Atom p => valuation p
| And a b => (eval a t valuation) /\ (eval b t valuation)
| Not p => not (eval p t valuation)
| Globally p => (forall t' , t' >= t -> (eval p t' valuation))
| Future p => (exists t' , t' >= t /\ (eval p t' valuation))
| Next p => (eval p (t + 1) valuation)
end.

(*
  Since ¬□¬p can be expressed by its dual ◇p, the Future evaluation 
  can be expressed thanks to the Globally and the Not evaluation. 
  This is illustrated by the following transformations and inductions:
     
  eval (Future p) t evaluation   
  ⟺ not (eval (Globally (Not p)) t evaluation)                  [Equivalence]
  ⟺ not (forall t',  t'>=t -> (eval (Not p) t' valuation))      [Induction]
  ⟺ exists t', not(t'>=t -> (eval (Not p) t' valuation))        [Forall-Not]
  ⟺ exists t', not(not(t'>=t) \/ (eval (Not p) t' valuation))   [Equivalence]
  ⟺ exists t', t'>=t /\ not(eval (Not p) t' valuation)          [Not distribution]
  ⟺ exists t', t'>=t /\ not(not(eval p t' valuation))           [Induction]
  ⟺ exists t', t'>=t /\ eval p t' valuation                     [DoubleNot*]

  * This is possible since not works on boolean which relies on the law of excluded middle.
*)                


(* Transitivity on order relation of TL ◇◇p → ◇p *)
Theorem future_trans: forall p t valuation, (eval (Future (Future p)) t valuation) -> (eval (Future p) t valuation).
Proof.
simpl;intros.
inversion H.
destruct H0.
inversion H1.
destruct H2.
exists x0.
split.
omega.
apply H3.
Qed.


(* Transitivity on order relation of TL ◇p → ◇◇p *)
Theorem future_trans2: forall p t valuation, (eval (Future p) t valuation) -> (eval (Future (Future p)) t valuation).
Proof.
simpl;intros.
inversion H.
destruct H0.
exists x.
intros; split.
apply H0.
exists x.
intros; split.
auto.
apply H1.
Qed.


(* Transitivity on order relation of TL □□p → □p *)
Theorem globally_trans: forall p t valuation, (eval (Globally (Globally p)) t valuation) -> (eval (Globally p) t valuation).
Proof.
  simpl.
  intros p t val H.
  apply H.
  omega.
Qed.


(* Transitivity on order relation of TL □p → □□p *)
Theorem globally_trans2: forall p t valuation, (eval (Globally p) t valuation) -> (eval (Globally (Globally p)) t valuation).
Proof.
  intros p t val H.
  simpl.
  intros.
  apply H.
  omega.
Qed.

(* Distributivity on next ◯(p ∨ q) → ◯p ∨ ◯q *)
Theorem next_distributivity_1: forall p q t valuation, (eval (Next (Or p q)) t valuation) -> (eval (Or (Next p) (Next q)) t valuation).
Proof.
simpl.
intros p q t val H.
assumption.
Qed.

(* Distributivity on next ◯p ∨ ◯q → ◯(p ∨ q) *)
Theorem next_distributivity_2: forall p q t valuation, (eval (Or (Next p) (Next q)) t valuation) -> (eval (Next (Or p q)) t valuation).
Proof.
simpl.
intros.
assumption.
Qed.

(* Distributivity on next ◯(p ∨ q) ≡ ◯p ∨ ◯q *)
Theorem next_distributivity: forall p q t valuation, (eval (Next (Or p q)) t valuation) <-> (eval (Or (Next p) (Next q)) t valuation).
Proof.
simpl.
intros.
split.
apply next_distributivity_1.
apply next_distributivity_2.
Qed.

(* Distributivity on globally □(p ∧ q) → □p ∧ □q *)
Theorem distributivity_globally_1: forall p q t valuation, (eval (Globally (And p q)) t valuation) -> (eval (And (Globally p) (Globally q)) t valuation).
Proof.
simpl.
intros p q t val H.
split.
intros.
apply H.
apply H0.
intros.
apply H.
apply H0.
Qed.

(* Distributivity on globally □p ∧ □q → □(p ∧ q) *)
Theorem distributivity_globally_2: forall p q t valuation, (eval (And (Globally p) (Globally q)) t valuation) -> (eval (Globally (And p q)) t valuation).
Proof.
simpl.
split.
intros.
apply H.
apply H0.
intros.
apply H.
apply H0.
Qed.

(* Distributivity on globally □(p ∧ q) ≡ □p ∧ □q *)
Theorem distributivity_globally: forall p q t valuation,  (eval (Globally (And p q)) t valuation) <-> (eval (And (Globally p) (Globally q)) t valuation).
Proof.
intros.
split.
apply distributivity_globally_1.
apply distributivity_globally_2.
Qed.


(* equiv globally *)

(* □p → ¬◇¬p *)
Theorem dual_nnpp_1: forall p t valuation, (eval (Globally p) t valuation) -> not (eval (Future (Not p)) t valuation).
Proof.
simpl.
intros p t valuation H H0.
inversion H0.
destruct H1.
apply H2.
apply H.
assumption.
Qed.

(* ¬◇¬p → □p *)
Theorem dual_nnpp_2: forall p t valuation, not (eval (Future (Not p)) t valuation) -> (eval (Globally p) t valuation).
Proof.
admit.
Admitted.

(* NNPP □p ≡ ¬◇¬p *)
Theorem nnpp: forall p t valuation, (eval (Globally p) t valuation) <-> not (eval (Future (Not p)) t valuation).
Proof.
admit.
Admitted.

(* equiv future *)

(* ◇p → ¬□¬p *)
Theorem dual_future_1: forall p t valuation, (eval (Future p) t valuation) -> not (eval (Globally (Not p)) t valuation).
Proof.
admit.
Admitted.

(* ¬□¬p → ◇p *)
Theorem dual_future_2: forall p t valuation, not (eval (Globally (Not p)) t valuation) -> (eval (Future p) t valuation).
Proof.
admit.
Admitted.

(* ◇p ≡ ¬□¬p *)
Theorem dual_future: forall p t valuation, (eval (Future p) t valuation) = not (eval (Globally (Not p)) t valuation).
Proof.
admit.
Admitted.

(* leads □p → ◇p *)
Theorem leads: forall p t valuation, (eval (Globally p) t valuation) -> (eval (Future p) t valuation).
Proof.
admit.
Admitted.
