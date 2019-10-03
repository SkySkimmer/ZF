Set Implicit Arguments.
Unset Strict Implicit.

Require Export ordinals.

Module AC.
Export Function. Export Map.

Definition is_choice_function x f := A (Function.axioms f)
(A (Function.domain f = Z (powerset x) (fun y => y<>emptyset))
(forall y, sub y x -> nonempty y -> inc (ev f y) y)).

Lemma ex_choice : forall x, ex (is_choice_function x).
Proof.
ir. exists (create (Z (powerset x) (fun y => y<>emptyset)) (fun a => rep a)).
uhg;ee. ap create_axioms. ap create_domain.
ir.

rw create_ev.
ap rep_inc. am.

ap Z_inc. ap powerset_inc. am.
uhg;ir. nin H0. apply emptyset_empty with x0.
wr H1;am.
Qed.


End AC.

Module Zorn.
Export AC. Export Order.

Definition is_inductive r a := A (is_order r a)
(forall b, sub b a -> is_total r b -> ex (is_upper_bound a r b)).

Definition is_preinductive r a := A (is_order r a)
(forall b, sub b a -> is_well_order r b -> ex (is_upper_bound a r b)).

Lemma inductive_preinductive : forall r a, is_inductive r a -> is_preinductive r a.
Proof.
uhg;ir;ee;au.
ir.
ap H. am. ap well_order_total. am.
Qed.

Section VarSec.

Variables (r : E2P) (a : E).

Hypothesis (Hi : is_preinductive r a).

Definition prechain b := A (sub b a)
(is_well_order r b).

Lemma prechain_upper : forall b, prechain b -> ex (is_upper_bound a r b).
Proof.
ir. ap Hi. am. am.
Qed.

End VarSec.

End Zorn.


