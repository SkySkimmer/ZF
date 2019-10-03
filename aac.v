
Set Implicit Arguments.
Unset Strict Implicit.

Require Export lci.

Require Import List.
Require Import Permutation.

Module AAC_tools.

Inductive list_sub : (list E) -> E -> Prop :=
  | sub_nil : forall x, list_sub nil x
  | sub_cons : forall x a t, inc a x -> list_sub t x -> list_sub (a::t) x
.


Fixpoint list_iter (op:E2) (def:E) (l: list E) := match l with
  | nil => def
  | x::nil => x
  | x::t => op x (list_iter op def t)
  end.


Lemma lci_list_inc : forall op x, is_lci op x -> forall def, inc def x -> 
forall l, list_sub l x -> inc (list_iter op def l) x.
Proof.
ir. nin H1.
simpl. am.
simpl. destruct t.
am.
ap H. am. ap IHlist_sub.
am. am.
Qed.

Lemma lci_list_nonempty_inc : forall op x, is_lci op x -> forall def l, list_sub l x -> l<>nil -> inc (list_iter op def l) x.
Proof.
ir. nin H0.
ap False_rect;au.

nin H2.
simpl. am.
change (inc (op a (list_iter op def (a0::t))) x).
ap H. am.
ap IHlist_sub. am. uhg;ir. inversion H4.
Qed.

Lemma list_sub_concat : forall x l l', list_sub l x -> list_sub l' x -> list_sub (l++l') x.
Proof.
ir. nin H. simpl;am.
simpl. constructor. am.
au.
Qed.

Lemma concat_list_sub : forall x l l', list_sub (l ++ l') x -> A (list_sub l x) (list_sub l' x).
Proof.
intros x.
assert (forall l0, list_sub l0 x -> forall l l', l0 = l ++ l' -> 
A (list_sub l x) (list_sub l' x)).

intros l0 H. nin H;ir.
destruct l;destruct l';simpl in H;try inversion H;simpl.
ee;constructor.

destruct l. simpl;ee. constructor.
simpl in H1. wr H1. constructor;am.

simpl in H1. inversion H1;subst.
cp (IHlist_sub l l' (eq_refl (l ++ l'))).
ee;au. constructor;am.

ir. eapply H. ap H0. tv.
Qed.

Definition force_nil : forall T:Type, list T.
ir. exact nil.
Defined.

Lemma Permutation_sub : forall x l, list_sub l x -> forall l', Permutation l l' -> list_sub l' x.
Proof.
ir. nin H0.
constructor.

inversion H;subst;constructor;au.

inversion H;subst. inversion H4;subst.
constructor;try am;constructor;am.

au.
Qed.

Ltac mk_iter_aux op a b l l' := match a with
  | op ?x ?a' => mk_iter_aux op a' b (x::l) l'
  | _ => match b with
    | op ?y ?b' => mk_iter_aux op a b' l (y::l')
    | _ => change (eq (list_iter op emptyset (rev (a::l))) (list_iter op emptyset (rev (b::l'))))
    end
  end.

Ltac mk_iter op := match goal with
  | |- eq ?a ?b => mk_iter_aux op a b (force_nil E) (force_nil E)
  | _ => assert True
  end.

(*step in solving Permutation (a::t) (l1++l1') by attempting to find an instance of a in l1'
and changing goal to (a::t) (l1 ++ a::l1')*)
Ltac Permchange a t l1 l1' := match l1' with 
  | cons a ?t' => change (Permutation (a::t) (l1 ++ a::t'))
  | cons ?b ?t' => Permchange a t (l1 ++ (b::nil)) t'
  end.

(*assumes lists are syntactic permutations, pre-simplified ! may fail if List.app terms present*)
Ltac solve_list_perm := match goal with 
  | |- Permutation ?l ?l' => try ap Permutation_refl;try (constructor;solve_list_perm);
match l with
  | cons ?a ?t => Permchange a t (force_nil E) l';ap Permutation_cons_app;simpl;solve_list_perm
  end
  end.

End AAC_tools.

Module AAC_all.
Export AAC_tools.

Lemma aac_perm_eq : forall op, (forall x y z, op x (op y z) = op (op x y) z) -> 
(forall x y, op x y = op y x) -> 
forall l l', Permutation l l' -> 
forall e, list_iter op e l = list_iter op e l'.
Proof.
ir. nin H1.
tv.
destruct l.
assert (l' = nil).
ap Permutation_nil. am. subst. tv.
destruct l'.
assert (e0::l = nil). ap Permutation_nil.
ap Permutation_sym. am.
inversion H2.
transitivity (op x (list_iter op e (e0::l))).
tv. rw IHPermutation. tv.
destruct l. simpl.
au.
transitivity (op y (op x (list_iter op e (e0::l)))).
tv. rw H. rw (H0 y). wr H. tv.
etransitivity;au.
Qed.

Ltac aa_normb_all Ha := repeat wr Ha.

Ltac aac_to_perm_all Ha Hc := try reflexivity;
match type of Hc with 
| (forall x y, ?op x y = ?op y x) => aa_normb_all Ha; mk_iter op; ap (aac_perm_eq Ha Hc);simpl
end.

Ltac aac_solve_all Ha Hc := aac_to_perm_all Ha Hc; solve_list_perm.

End AAC_all.

Module AAC_lci.
Export AAC_tools.


Lemma aac_perm_eq : forall op x, is_lci op x -> associative op x -> commutative op x -> 
forall l l', list_sub l x -> Permutation l l' -> forall e,
list_iter op e l = list_iter op e l'.
Proof.
ir. cp (Permutation_sub H2 H3). nin H3.
tv.

destruct l as [nil | x1 t].
apply Permutation_nil in H3. subst.
tv.
destruct l' as [nil | x1' t'].
symmetry in H3. apply Permutation_nil in H3. inversion H3.

change (op x0 (list_iter op e (x1::t)) = op x0 (list_iter op e (x1'::t'))).
rw IHPermutation.
tv. inversion H2;subst;au.
inversion H4;subst;au.

destruct l.
simpl. inversion H2;subst.  inversion H8;subst. ap H1;au.

transitivity (op y (op x0 (list_iter op e (e0::l)))).
simpl;tv.
transitivity (op x0 (op y (list_iter op e (e0::l)))).
assert (inc x0 x). inversion H4;subst;au.
assert (inc y x). inversion H4;subst;au.
inversion H2;au.
assert (inc (list_iter op e (e0::l)) x).
ap lci_list_nonempty_inc. am. inversion H2;subst;inversion H10;subst;au.
uhg;ir. inversion H6.

transitivity (op (op y x0) (list_iter op e (e0::l))).
rw H0;au.
rw (H1 y H5 x0 H3). rw H0;au.

simpl. tv.

cp (Permutation_sub H2 H3_).
rw IHPermutation1. ap IHPermutation2.
am. am. am. am.
Qed.

Ltac solve_lci_inc Hlci := first [ ap Hlci; solve_lci_inc Hlci | am | tv].

Ltac aa_normb_lci Hlci Ha := try (wr Ha;[aa_normb_lci Hlci Ha | solve_lci_inc Hlci | solve_lci_inc Hlci | solve_lci_inc Hlci]).

Ltac uf_list_sub := simpl;match goal with 
   | |- list_sub nil _ => constructor
   | |- list_sub _ _ => constructor;[idtac | uf_list_sub]
  end.

Ltac aac_to_perm_lci op Hlci Ha Hc := try reflexivity;
aa_normb_lci Hlci Ha; mk_iter op; ap (aac_perm_eq Hlci Ha Hc);simpl;[uf_list_sub | idtac]
.

Ltac aac_solve_lci op Hlci Ha Hc := aac_to_perm_lci op Hlci Ha Hc; simpl;try solve_list_perm
.

Ltac aac_solve_monoid Hmon Hc := match type of Hmon with
  | is_monoid ?op _ _ => aac_solve_lci op (and_P Hmon) (and_Q (and_Q Hmon)) Hc
  | is_group ?op _ _ =>  aac_solve_lci op (and_P Hmon) (and_P (and_Q (and_Q Hmon))) Hc
  end.

End AAC_lci.



