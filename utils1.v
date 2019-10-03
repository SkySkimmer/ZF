
Set Implicit Arguments.
Unset Strict Implicit.

Require Export nnum_base.

(*
Additional results for various stuffs
*)

Module Utils1.

Section VarSec1.

Variables (pl ml : E2) (g : E) (e u : E).

Hypothesis (Hring : is_ring pl ml g e u).

Notation opp := (Lci.inverse_of pl g e).
Notation inv := (Lci.inverse_of ml g u).

Lemma ring_distrib_l : distrib_l pl ml g.
Proof.
am.
Qed.

Lemma ring_distrib_r : distrib_r pl ml g.
Proof.
am.
Qed.

Lemma ring_inverses_switch : forall x y,
Lci.are_inverse pl g e x y -> forall z, Lci.are_inverse ml g u x z -> 
forall k, Lci.are_inverse ml g u y k = Lci.are_inverse pl g e z k.
Proof.
ir. ap iff_eq;ir;uh H;uh H0;uh H1;ee.

uhg;ee;try am.
assert (is_neutre ml g u). ap Hring.
uh H11;ee. 
wr (H12 z H3). wr H5.
assert (associative ml g). ap Hring.
rw H14;au.
transitivity (pl (ml (ml z y) k) (ml u k)).
ap uneq. symmetry;au.
wr ring_distrib_r;au.
wr H8.
wr ring_distrib_l;au. rw H10. 
rw (ring_0_multr Hring);au.
ap (ring_0_multl Hring). am.
ap Hring;am.

assert (is_neutre ml g u). ap Hring.
uh H11;ee. 
wr (H12 z H3). wr H5.
assert (associative ml g). ap Hring.
rw H14;au.
transitivity (pl (ml u k) (ml (ml z y) k)).
ap uneq2;au. symmetry;au.
wr ring_distrib_r;au.
wr H8.
wr ring_distrib_l;au. rw H9. 
rw (ring_0_multr Hring);au.
ap (ring_0_multl Hring). am.
ap Hring;am.

uhg;ee;try am.
assert (y = opp x).
ap inverse_of_eq. ap group_is_monoid;am.
uhg;ee;am.
assert (k = opp z).
ap inverse_of_eq. ap group_is_monoid;am.
uhg;ee;am.
rw H11;rw H12.
wr (inverse_ml_insert_right Hring).
wr (inverse_ml_insert_left Hring).
wr inverse_inverse.
am. am. ap Hring;am.
am. am. wr H11. am. am.

assert (y = opp x).
ap inverse_of_eq. ap group_is_monoid;am.
uhg;ee;am.
assert (k = opp z).
ap inverse_of_eq. ap group_is_monoid;am.
uhg;ee;am.
rw H11;rw H12.
wr (inverse_ml_insert_right Hring).
wr (inverse_ml_insert_left Hring).
wr inverse_inverse.
am. am. ap Hring;am.
am. am. wr H12. am. am.
Qed.

Lemma ring_opp_inv : forall x, inversible ml g u x -> opp (inv x) = inv (opp x).
Proof.
ir.
apply inversible_inverse_of in H.
Focus 2. am.
assert (inc x g). am.
assert (is_group pl g e). am.
cp (group_inverse_of H1 H0).
cp (ring_inverses_switch H2 H).
assert (inc (inv x) g). am.
apply (group_inverse_of H1) in H4.
cp H4. wri H3 H5. clear H3.
ap inverse_of_eq. am. am.
Qed.

End VarSec1.

Section VarSec2.

Variables (pl ml : E2) (g e u : E).

Lemma ring_prove_commut : is_monoid pl g e -> is_regular pl g -> 
is_monoid ml g u -> distributes pl ml g -> 
commutative pl g.
Proof.
uhg;ir.
assert (pl (pl x x) (pl y y) = pl (pl x (pl y x)) y).
transitivity (ml (pl x y) (pl u u));uh H2;ee.
symmetry. rw H5;au.
rw H2;au. rw H2;au.
ap uneq2;ap uneq2;ap H1;am.
ap H;am.
rw H2;au. rw H5;au.
assert (is_neutre ml g u). am.
uh H6;ee. rw H7;au. rw H7;au.
assert (associative pl g). am. assert (is_lci pl g). am.
uh H10.
wr H9;au. wr H9;au. wr H9;au.
ap H;am.
uh H0;ee.
apply H0 with x;au. ap H;am. ap H;am.
apply H6 with y;au. ap H. am. ap H;am.
ap H. am. ap H;am.
wr H5.
uh H;ee. uh H.
rw H8;au. rw H8;au.
Qed.

End VarSec2.

Lemma axioms_emptyset_eq : forall f, axioms f -> domain f = emptyset -> 
f = emptyset.
Proof.
ir. uh H;ee.
ap empty_emptyset.
ir. cp H2;apply H in H3.
nin H3.
assert (inc a (domain f)). ap domain_inc. exists b;am.
rwi H0 H3. apply emptyset_empty in H3;am.
Qed.

(*
predecessor
*)
Definition pred x := union x.

Lemma pred_0 : pred n0 = n0.
Proof.
uf n0;ap empty_emptyset.
ir. ufi pred H. apply union_ex in H. nin H;ee.
eapply emptyset_empty;am.
Qed.

Lemma pred_S : forall n, inc n nNum -> pred (oS n) = n.
Proof.
ir. ap ordinal_union_S. ap nNum_ordinal;am.
Qed.

Lemma emptyset_range : range emptyset = emptyset.
Proof.
ap empty_emptyset. ir.
apply Im_ex in H. nin H;ee;apply Z_sub in H. emptyset_auto.
Qed.

Lemma nNum_S_S_inc : forall n, inc n nNum -> forall m, inc m nNum -> 
inc (oS n) (oS m) -> inc n m.
Proof.
ir.
wr nLt_inc_rw;nSolveS. rw nLt_S_S;nSolveS.
rw nLt_inc_rw;nSolveS.
Qed.

Lemma nNum_inc_S_S : forall n m, inc m nNum ->
inc n m -> inc (oS n) (oS m).
Proof.
ir.
cp (omega_transitiveT H H0).
wr nLt_inc_rw;nSolveS. wr nLt_S_S;nSolveS.
rw nLt_inc_rw;nSolveS.
Qed.

Lemma tack_on_inc_eq : forall x y, inc y x -> tack_on x y = x.
Proof.
ir. ap extensionality;uhg;ir.
rwi tack_on_inc H0. nin H0;subst;am.
rw tack_on_inc;au.
Qed.

Lemma trans_bijective_fast : forall a b f, 
(forall x, inc x a -> forall y, inc y a -> f x = f y -> (inc (f x) b & x=y)) -> 
(forall y, inc y b -> exists x, inc x a & f x = y) -> 
Application.bijective a b f.
Proof.
ir;uhg;ee;uhg;ir.
cp (H x H1 x H1).
ap H2. tv.
ap H. am. am. am.
ap H0. am.
Qed.

Lemma nLeq_nPlus_l : forall n, inc n nNum -> forall m, inc m nNum -> 
nLeq n (nPlus n m).
Proof.
ir. assert (nLeq (nPlus n n0) (nPlus n m)).
ap nLeq_nPlus_compat;nSolveS.
rwi nPlus_0 H1. am. am.
Qed.

Lemma n0_inc_S : forall n, inc n nNum -> inc n0 (oS n).
Proof.
ir. wr nLt_inc_rw;nSolveS;rw nLt_S_rw;nSolveS;wr nLeq_S_S;nSolveS.
Qed.

Lemma nonempty_card : forall x, nonempty x = sub n1 (card x).
Proof.
ir.
assert (is_ordinal (card x)). ap Sow.sow_ordinal.
assert (is_ordinal n1). ap nNum_ordinal;nSolveS.
destruct ordinal_inc_eq_inc with (card x) n1.
am. am.
ufi n1 H1. rwi oS_inc H1.
nin H1. apply emptyset_empty in H1;nin H1.
ap iff_eq;ir.
nin H2.
cp (card_equipotent x).
nin H3. apply (bijective_of_map H3) in H2.
rwi H1 H2;apply emptyset_empty in H2;nin H2.
assert (inc emptyset (card x)).
ap H2. uf n1;rw oS_inc;au.
rwi H1 H3. apply emptyset_empty in H3;nin H3.
nin H1.
ap iff_eq;ir.
rw H1;ap sub_refl.
cp (card_equipotent x).
rwi H1 H3. nin H3.
assert (inc n0 n1).
uf n0;uf n1;rw oS_inc;au.
apply H3 in H4. nin H4;ee.
exists x1;am.
ap iff_eq;ir.
apply ordinal_inc_sub in H1. am.
am.
assert (inc n0 n1).
uf n0;uf n1;rw oS_inc;au.
cp (card_equipotent x).
nin H4.
apply H2 in H3. apply H4 in H3.
nin H3;ee;exists x1;am.
Qed.

Lemma union_Im_cond_strict : forall f f' a, 
(forall x, inc x a -> forall x', inc x' a -> forall z, inc z (f x) -> inc z (f x') -> x=x') -> 
forall g, (forall x, inc x a -> bijective (f x) (f' x) (g x)) ->
forall h h', inc h (Im g a) -> inc h' (Im g a) -> 
nonempty (inter2 (domain h) (domain h')) -> h = h'.
Proof.
ir.
Im_nin H1;Im_nin H2;subst.
cp (H0 x H1);cp (H0 x0 H2).
assert (domain (g x) = f x). uh H4;ee;ap H4.
assert (domain (g x0) = f x0). uh H5;ee;ap H5.
rwi H6 H3;rwi H7 H3.
nin H3.
apply inter2_and in H3;ee.
ap uneq.
eapply H. am. am. am. am.
Qed.

Lemma union_Im_bijective : forall f f' a, 
(forall x, inc x a -> forall x', inc x' a -> forall z, inc z (f x) -> inc z (f x') -> x=x') -> 
(forall x, inc x a -> forall x', inc x' a -> forall z, inc z (f' x) -> inc z (f' x') -> x=x') -> 
forall g, (forall x, inc x a -> bijective (f x) (f' x) (g x)) ->
bijective (union (Im f a)) (union (Im f' a)) (union (Im g a)).
Proof.
ir.
pose (e := (Im g a)).
assert (forall h, inc h e -> exists x, inc x a & bijective (f x) (f' x) h).
ir. Im_nin H2. subst.
exists x;ee;au.
assert (forall h, inc h e -> axioms h).
ir;apply H2 in H3. nin H3;ee;am.
assert (forall x, inc x a -> domain (g x) = (f x)).
ap H1.
assert (union_strict_cond e). rw union_strict_cond_rw.
ir.
Im_nin H5;Im_nin H6;subst.
rwi H4 H7;try am; rwi H4 H7;try am.
nin H7. apply inter2_and in H7;ee.
ap uneq. apply H with x1;am.
cp (union_axioms H3 H5).
cp (union_domain H3 H5).
cp (union_range H3 H5).
cp (union_ev H3 H5).
clear H2 H3 H5.
assert (forall x, inc x a -> forall k, inc k (f x) -> ev (union e) k = ev (g x) k).
ir.
assert (inc k (domain (g x))). rw H4;au.
apply H9 in H5. am.
ap Im_inc. am. clear H9.
uhg;ee. 
uhg;ir;ee.
am.
ufi e H7;rw H7.
ap extensionality_rw.
intros k.
ap iff_eq;ir.
union_nin H3. Im_nin H3;subst.
Im_nin H3. subst. rwi H4 H5;try am.
ap union_inc. econstructor;ee. ap Im_inc. am.
am.
union_nin H3. Im_nin H3;subst.
ap union_inc. econstructor;ee. 
ap Im_inc. ap Im_inc. am.
rw H4. am. am.
rw range_Im_rw;try am.
uhg;ir.
Im_nin H3.
subst. ufi e H7;rwi H7 H3.
union_nin H3. Im_nin H3;subst. Im_nin H3;subst.
rwi H4 H5;try am.
ufi e H2.
rw (H2 x0 H3 x H5). ap union_inc. econstructor.
ee. ap Im_inc. am. eapply trans_of_map. ap H1. am.
am.
uhg;ir.
union_nin H3. Im_nin H3;subst.
union_nin H5;Im_nin H5;subst.
ufi e H2;rwi (H2 x1 H3 x H10) H9;rwi (H2 x2 H5 y H11) H9.
cp (H1 x1 H3);cp (H1 x2 H5).
cp H10. apply (bijective_of_map H12) in H14.
cp H11. apply (bijective_of_map H13) in H15.
rwi H9 H14.
assert (x1 = x2).
apply H0 with (ev (g x2) y);am.
subst.
apply H13;am.

uhg;ir.
union_nin H3. Im_nin H3. subst.
cp (H1 x0 H3).
cp H5. apply H9 in H10. nin H10;ee;subst.

econstructor;ee. ap union_inc;econstructor. ee.
ap Im_inc. am. am.
ufi e H2. rw (H2 x0 H3 x H10). tv.
Qed.


(*
functions on nats as lists
*)
Module EList.

Definition is_elist l := A (Function.axioms l) (inc (domain l) nNum).

Definition enil := emptyset.

Definition list_length l := domain l.

Lemma list_length_inc : forall l, is_elist l -> inc (list_length l) nNum.
Proof.
ir;am.
Qed.

Lemma is_elist_nil : is_elist enil.
Proof.
uhg;ee.
ap emptyset_axioms.
uf enil;rw emptyset_domain. nSolveS.
Qed.

Lemma nil_length : list_length enil = n0.
Proof.
ap emptyset_domain.
Qed.

Definition econs x l := L (oS (list_length l)) (fun n => by_cases
(fun _ : n=n0 => x)
(fun _ : _ => ev l (pred n))).

Lemma econs_length : forall x l, list_length (econs x l) = oS (list_length l).
Proof.
ir. ap create_domain.
Qed.

Lemma econs_0 : forall l, is_elist l -> forall x, ev (econs x l) n0 = x.
Proof.
ir.
uf econs. rw create_ev.
rw by_cases_if. tv. tv.
uh H. uf list_length.
ap ordinal_inc_S_all. ap nNum_ordinal;am.
Qed.

Lemma econs_S : forall l, is_elist l -> forall n, inc n (list_length l) -> forall x, 
ev (econs x l) (oS n) = ev l n.
Proof.
ir.
assert (inc n nNum).
cp omega_ordinal. uh H1. ee.
eapply H1. Focus 2. am.
am.

 uf econs;rw create_ev.
rw by_cases_if_not. rw pred_S. tv.
am. ap oS_emptyset_neq.
ap ordinal_S_inc_inc. ap nNum_ordinal;am.
ap nNum_ordinal;am.
am.
Qed.

Lemma econs_list : forall l, is_elist l -> forall x, is_elist (econs x l).
Proof.
ir. uhg;ee. ap create_axioms.
uf econs. rw create_domain. nSolveS.
Qed.

Lemma econs_inj : forall l, is_elist l -> forall l', is_elist l' -> 
forall x y, econs x l = econs y l' -> A (x=y) (l=l').
Proof.
ir. ee.
cp (uneq (fun f => ev f n0) H1). simpl in H2.
rwi econs_0 H2. rwi econs_0 H2. am.
am. am.

assert (list_length l = list_length l').
cp (uneq list_length H1).
rwi econs_length H2. rwi econs_length H2.
ap oS_N_inj. am. am.
ap function_extensionality. am. am. am.
ir.
cp (uneq (fun l => ev l (oS x0)) H1). simpl in H4.
rwi econs_S H4. rwi econs_S H4. am.
am. wr H2;am. am. am.
Qed.

Definition tail l := L (pred (list_length l)) (fun n => ev l (oS n)).

Lemma tail_list : forall l, is_elist l -> is_elist (tail l).
Proof.
ir. uhg;ee. ap create_axioms.
uf tail. rw create_domain. 
uh H;ee. uf list_length. apply nNum_destruct in H0.
 nin H0.
rw H0. fold n0. rw pred_0. nSolveS.
nin H0;ee. rw H1. rw pred_S;au.
Qed.

Lemma tail_nil : tail enil = enil.
Proof.
uf tail. rw nil_length. rw pred_0.
ap function_extensionality. ap create_axioms. ap emptyset_axioms.
rw create_domain. symmetry.
ap nil_length.
ir. rwi create_domain H. apply emptyset_empty in H. nin H.
Qed.

Lemma tail_length : forall l, list_length (tail l) = pred (list_length l).
Proof.
ir;ap create_domain.
Qed.

Lemma elist_destruct : forall l, is_elist l -> (l=enil \/ exists x,exists tl, is_elist tl & l = econs x tl).
Proof.
ir.
uh H;ee.
apply nNum_destruct in H0. nin H0.
left. ap function_extensionality.
am. ap emptyset_axioms.
rw H0;symmetry;ap emptyset_domain.
ir. rwi H0 H1;apply emptyset_empty in H1;nin H1.

nin H0;ee;subst.
right.
exists (ev l n0).
exists (tail l).
ee. ap tail_list. uhg. ee. am. rw H1;nSolveS.

ap function_extensionality.
am.
ap econs_list. ap tail_list. uhg;ee.
am. rw H1;nSolveS.
uf econs;rw create_domain. uf list_length;uf tail.
rw create_domain. uf list_length. rw H1.
ap uneq. symmetry. ap pred_S;am.

ir.
assert (inc x0 nNum).
cp omega_ordinal. uh H3;ee. eapply H3.
Focus 2. ap H2. rw H1. nSolveS.
apply nNum_destruct in H3. nin H3.
subst. rw econs_0. reflexivity.
ap tail_list. uhg;ee. am. rw H1;nSolveS.
nin H3;ee;subst.
rw econs_S. uf tail. rw create_ev.
tv.
uf list_length. rw H1. rw pred_S. rwi H1 H2.
wr nLt_inc_rw;au. wri nLt_inc_rw H2;nSolveS.
rw nLt_S_S;nSolveS.
am. ap tail_list;uhg;ee. am. rw H1;nSolveS.
rw tail_length. uf list_length. rw H1. rw pred_S;nSolveS.
rwi H1 H2.
wr nLt_inc_rw;au. wri nLt_inc_rw H2;nSolveS.
rw nLt_S_S;nSolveS.
Qed.

Lemma tail_cons : forall l, is_elist l -> forall x, tail (econs x l) = l.
Proof.
ir.
ap function_extensionality.
ap create_axioms. am.
uf tail;rw create_domain. rw econs_length.
rw pred_S;try am. reflexivity.
ir.

ufi tail H0;rwi create_domain H0.
uf tail;rw create_ev;try am.
rwi econs_length H0. rwi pred_S H0;try am.
rw econs_S. tv.
am. am.
Qed.

Lemma length_0_nil : forall l, is_elist l -> list_length l = n0 -> l = enil.
Proof.
ir. apply elist_destruct in H. nin H. am.
nin H;nin H;ee;subst.
rwi econs_length H0. apply oS_emptyset_neq in H0. nin H0.
Qed.

Inductive elist_lt : E2P :=
  | elist_lt_cons : forall x l, is_elist l -> elist_lt l (econs x l)
.

Lemma elist_lt_wf : well_founded elist_lt.
Proof.
uf well_founded.
pose (p n := forall l, is_elist l -> list_length l = n -> Acc elist_lt l).
assert (forall n, inc n nNum -> p n). ap nNum_rect;uf p;clear p.
ir. assert (l = enil).
ap length_0_nil. am. am.
subst. constructor.
ir. inversion H1;subst.
wri H2 H0. rwi econs_length H0.
apply oS_emptyset_neq in H0. nin H0.
ir.
constructor. ir.
inversion H3;subst.
rwi econs_length H2. apply oS_N_inj in H2;try am.
ap H0. am. am.

ir. apply by_cases with (is_elist a);ir.
eapply H. am. am. reflexivity.
constructor. ir. inversion H1;subst.
nin H0. ap econs_list. am.
Qed.

Lemma list_not_nil : forall l, is_elist l -> l<>enil -> 
l = econs (ev l n0) (tail l).
Proof.
ir.
apply elist_destruct in H;nin H. nin H0;am.
nin H;nin H;ee.
etransitivity. am. ap uneq2.
cp (uneq (fun l' => ev l' n0) H1).
simpl in H2. rwi econs_0 H2. au. am.

symmetry in H1. cp (uneq tail H1).
rwi tail_cons H2. am. am.
Qed.

Lemma elist_lt_inv : forall l, is_elist l -> forall x l', elist_lt l' (econs x l) -> l' = l.
Proof.
ir. inversion H0;subst.
apply econs_inj in H1. am. am. am. 
Qed.

Definition elist_rec : forall P : Type,
P -> 
(forall l : E, P -> forall x : E, P) -> 
(forall l : E, P) -> 
forall l : E, P.
intros P Hnil IH Hreb.
eapply Fix. ap elist_lt_wf.
ir.
apply by_cases with (x=enil);ir.
ap Hnil.
apply by_cases with (is_elist x);ir.
eapply IH. exact (tail x).
apply X with (tail x).
cp (tail_list H0). apply list_not_nil in H.
assert (elist_lt (tail x) (econs (ev x n0) (tail x))). constructor. am.
wri H H2. am.
am.
exact (ev x n0).
eapply Hreb. exact x.
Defined.

Lemma elist_rec_nil : forall P (Hnil : P) IH Hreb, elist_rec Hnil IH Hreb enil = Hnil.
Proof.
ir. uf elist_rec. rw Fix_eq. rw by_cases_if. tv. tv.
ir. ap uneq. 
ap arrow_extensionality. ir.
ap uneq2. ap arrow_extensionality;ir.
rw H. tv.
tv.
Qed.

Lemma elist_rec_not : forall P (Hnil : P) IH Hreb, forall l (Hnot : ~ is_elist l),
elist_rec Hnil IH Hreb l = Hreb l.
Proof.
ir. uf elist_rec. rw Fix_eq. rw by_cases_if_not.
erewrite by_cases_if_not. reflexivity.
uhg;ir;ap Hnot. subst.  am.
uhg;ir. ap Hnot;subst;ap is_elist_nil.
ir. ap uneq.
ap arrow_extensionality. ir.
ap uneq2. ap arrow_extensionality;ir.
rw H. tv.
tv.
Qed.

Lemma elist_rec_cons : forall P (Hnil : P) IH Hreb, forall l (Hl : is_elist l) x, 
elist_rec Hnil IH Hreb (econs x l) = IH l (elist_rec Hnil IH Hreb l) x.
Proof.
ir. uf elist_rec. rw Fix_eq.
rw by_cases_if_not. erewrite by_cases_if.
rw tail_cons.
ap uneq. ap econs_0. am. am.
ap econs_list;am.
uhg;ir.
cp (uneq list_length H). 
rwi econs_length H0. rwi nil_length H0.
eapply oS_emptyset_neq. am.
ir. ap uneq.
ap arrow_extensionality. ir.
ap uneq2. ap arrow_extensionality;ir.
rw H. tv.
tv.
Qed.

Lemma elist_ind : forall P : EP,
P enil -> 
(forall l, is_elist l -> P l -> forall x, P (econs x l)) -> 
forall l, is_elist l -> P l.
Proof.
intros P Hnil IH.
intro l. cp (elist_lt_wf l). nin H.
ir. apply by_cases with (x=enil);ir.
subst. am.
apply list_not_nil in H2. rw H2. ap IH. ap tail_list;am.
ap H0. assert (elist_lt (tail x) (econs (ev x n0) (tail x))). constructor.
ap tail_list;am. wri H2 H3. am.
ap tail_list;am.
am.
Qed.

Definition fold_right (f : E2) (l a : E) : E.
ap elist_rec. exact a.
intros tl r x.
exact (f x r).
ir. exact a.
exact l.
Defined.

Lemma fold_right_not : forall f l a, ~ is_elist l -> fold_right f l a = a.
Proof.
ir. uf fold_right.  rw elist_rec_not. tv. am.
Qed.

Lemma fold_right_nil : forall f a, fold_right f enil a = a.
Proof.
ir; ap elist_rec_nil.
Qed.

Lemma fold_right_cons : forall x l, is_elist l -> forall f a, 
fold_right f (econs x l) a = f x (fold_right f l a).
Proof.
ir;uf fold_right.
rw elist_rec_cons. tv. am.
Qed.

Definition list_of l a := exists n, inc n nNum & is_map n a l.

Lemma list_of_list : forall l a, list_of l a -> is_elist l.
Proof.
ir. nin H;ee. uhg. ee. am. uh H0;ee. rw H1. am.
Qed.

Lemma list_of_inc : forall l a, list_of l a -> forall n, inc n (list_length l) -> 
inc (ev l n) a.
Proof.
ir. nin H. ee. replace (list_length l) with x in *.
eapply trans_of_map. am. am.
symmetry;am.
Qed.

Lemma nil_list_of : forall a, list_of enil a.
Proof.
ir;exists n0;ee. nSolveS.
uhg;ee. ap emptyset_axioms. ap emptyset_domain.
uhg;ir.
ufi enil H. rwi emptyset_range H. emptyset_auto.
Qed.

Lemma cons_list_of : forall a x, inc x a -> forall l, list_of l a -> 
list_of (econs x l) a.
Proof.
ir. nin H0. ee.
exists (oS x0). ee.
nSolveS.
assert (x0 = (list_length l)).
symmetry;am.
assert (forall x1, inc x1 (oS x0) -> inc x1 nNum).
ap omega_ordinal. nSolveS.

rw H2. ap map_of_trans.
uhg;ir. apply by_cases with (x1=n0);ir.
rw by_cases_if. am. am.
rw by_cases_if_not.
rwi H2 H3.
cp (H3 x1 H4).
apply nNum_destruct in H6. nin H6. nin H5;am.
nin H6;ee;subst.
rw pred_S. eapply trans_of_map. am.
wr nLt_inc_rw;try am. rw nLt_S_S;try am.
rw nLt_inc_rw;nSolveS. am.
am.
Qed.

Lemma list_of_tail : forall a l, list_of l a -> list_of (tail l) a.
Proof.
ir.
assert (is_elist l). eapply list_of_list. am.
apply by_cases with (l = enil);ir. subst.
rw tail_nil. ap nil_list_of.
nin H;ee. apply nNum_destruct in H. nin H.
nin H1. apply length_0_nil. am.
uf n0;wr H. am.
nin H;ee;subst.
exists x0. ee. am.
uf tail. assert (list_length l = oS x0).
am.
rw H3. rw pred_S.
ap map_of_trans. uhg;ir.
eapply trans_of_map. am.
assert (inc x nNum). cp omega_ordinal. uh H5;ee;eapply H5.
ap H. am.
wr nLt_inc_rw;nSolveS. wr nLt_S_S;nSolveS. rw nLt_inc_rw;nSolveS.
am.
Qed.

Lemma list_list_of : forall l, is_elist l -> forall a, Application.axioms (list_length l) a (ev l) -> 
list_of l a.
Proof.
ir.
exists (list_length l). ee.
am.
uhg;ee. am.
tv.
rw range_Im_rw. uhg;ir.
Im_nin H1. subst. ap H0. am.
am.
Qed.

Lemma list_of_cons : forall a x l, is_elist l -> list_of (econs x l) a -> 
A (inc x a) (list_of l a).
Proof.
ir. nin H0. nin H0.
apply nNum_destruct in H0. nin H0.
ap False_rect. subst.
assert (list_length (econs x l) = n0). am.
rwi econs_length H0. eapply oS_emptyset_neq;am.
nin H0;nin H0;subst.
assert (forall x0, inc x0 x1 -> inc x0 nNum). ap omega_ordinal. am.
ee. replace x with (ev (econs x l) n0). eapply trans_of_map.
am. wr nLt_inc_rw;nSolveS. rw nLt_S_rw;nSolveS.
wr nLeq_S_S;nSolveS.
ap econs_0. am.
ap list_list_of. am.
uhg;ir.
replace (ev l x0) with (ev (econs x l) (oS x0)).
eapply trans_of_map. am. 
assert (inc x0 nNum). cp (omega_ordinal).
uh H4;ee;eapply H4. ap H. am.
wr nLt_inc_rw;nSolveS. wr nLt_S_S;nSolveS.
rw nLt_inc_rw;nSolveS.
replace x1 with (list_length l). am.
eapply oS_N_inj. ap H.
wr (econs_length x). am.
rw econs_S. tv. am. am.
Qed.

Lemma fold_right_inc : forall a b f, (forall x, inc x a -> forall y, inc y b -> inc (f x y) b) -> 
forall l, list_of l a -> forall r, inc r b -> inc (fold_right f l r) b.
Proof.
intros a b f Hf.
pose (p l := list_of l a -> forall r : E, (r ∈ b) -> (fold_right f l r ∈ b)).
assert (forall l, is_elist l -> p l).
ap elist_ind;uf p;clear p;ir.
rw fold_right_nil. am.
rw fold_right_cons. ap Hf. apply list_of_cons in H1. am.
am.
ap H0. apply list_of_cons in H1. am.
am. am. am.

ir. ap H. eapply list_of_list. am. am. am.
Qed.

Lemma trans_of_list : forall l a, list_of l a -> Application.axioms (list_length l) a (ev l).
Proof.
ir. nin H;ee. replace (list_length l) with x. ap trans_of_map. am.
symmetry. am.
Qed.

(*
fold_left f a nil = a
fold_left f a (x::tl) = fold_left f (f a x) tl
*)

Definition fold_left : E2 -> E2.
intro f.
assert (E -> E1).
(* l => a => fold_left f a l*)
ap (elist_rec (P := E1)).
exact (fun a => a).
intros tl rtl x a. (* rtl = fun z => fold_left f z tl *)
exact (rtl (f a x)).
intros notL a. exact a.
intros a l. exact (X l a). 
Defined.

Lemma fold_left_not : forall l, ~ is_elist l -> forall f a, fold_left f a l = a.
Proof.
ir. uf fold_left. rw elist_rec_not. tv. am.
Qed.

Lemma fold_left_nil : forall f a, fold_left f a enil = a.
Proof.
ir. uf fold_left;rw elist_rec_nil. tv.
Qed.

Lemma fold_left_cons : forall l, is_elist l -> forall x f a, 
fold_left f a (econs x l) = fold_left f (f a x) l.
Proof.
ir. uf fold_left.
rw elist_rec_cons. tv.
am.
Qed.

Definition rev l := fold_left (fun r x => econs x r) enil l.

Lemma rev_nil : rev enil = enil.
Proof.
uf rev. rw fold_left_nil. tv.
Qed.

Lemma rev_nil_aux : forall l, fold_left (fun r x => econs x r) l enil = l.
Proof.
ir. ap fold_left_nil. 
Qed.

Lemma rev_cons_aux : forall l x l', is_elist l' -> 
fold_left (fun r x => econs x r) l (econs x l') = fold_left (fun r x => econs x r) (econs x l) l'.
Proof.
ir. rw fold_left_cons. tv. am.
Qed.

Inductive is_elist_alt : EP :=
  | nil_elist_alt : is_elist_alt enil
  | cons_elist_alt : forall l, is_elist_alt l -> forall x, is_elist_alt (econs x l).

Lemma elist_alt_eq : is_elist =is_elist_alt.
Proof.
ap arrow_extensionality.
assert (forall a, is_elist a -> is_elist_alt a). ap elist_ind.
constructor. ir. constructor. am.
ir. ap iff_eq;ir. au.
nin H0. ap is_elist_nil. ap econs_list. am.
Qed.

Lemma rev_aux_ev_end : forall l', is_elist l' ->  forall l, is_elist l -> 
forall n, inc n (list_length l) -> 
ev (fold_left (fun r x => econs x r) l l') (nPlus (list_length l') n) = ev l n.
Proof.
intros l' Hl'. cp Hl'. rwi elist_alt_eq H. nin H.
ir. rw nil_length. rw nPlus_0_l. rw fold_left_nil. tv.
cp (omega_ordinal). uh H1;ee;eapply H1. ap H. tv.
wri elist_alt_eq H.
cp (IHis_elist_alt H). clear IHis_elist_alt.
ir.
assert (inc n nNum). cp omega_ordinal. uh H3;ee;eapply H3. ap H1. am.
 rw fold_left_cons.
rw econs_length. rw nPlus_S_l. wr nPlus_S. rw H0.
rw econs_S. tv. am. am. ap econs_list. am.
rw econs_length. wr nLt_inc_rw;nSolveS.
wr nLt_S_S;nSolveS. rw nLt_inc_rw;nSolveS.
am. am. am. am. am.
Qed.

Lemma rev_aux_ev_begin : forall l', is_elist l' -> forall l, is_elist l -> 
forall n, inc n nNum -> forall k, inc k nNum -> 
list_length l' = oS (nPlus n k) -> 
ev (fold_left (fun r x => econs x r) l l') n = ev l' k.
Proof.
intros l' Hl'.
 cp Hl'. rwi elist_alt_eq H. nin H.
ir. rwi nil_length H2.
symmetry in H2;apply oS_emptyset_neq in H2;nin H2.

cp H. wri elist_alt_eq H0.
cp (IHis_elist_alt H0). clear IHis_elist_alt.
intro l'. ir.
rwi econs_length H5. apply oS_N_inj in H5;nSolveS.
rw fold_left_cons.
apply nNum_destruct in H4;nin H4. subst.
rwi nPlus_0 H5. subst.
wr (nPlus_0 H3). rw rev_aux_ev_end. rw econs_0. rw econs_0.
tv. am. am. am. ap econs_list;am.
rw econs_length. wr nLt_inc_rw;nSolveS.
rw nLt_S_rw;nSolveS. wr nLeq_S_S;nSolveS. am.
destruct H4 as [k' H4];ee;subst.
rwi nPlus_S H5;nSolveS.
erewrite H1. rw econs_S. ap eq_refl.
am. 
wr nLt_inc_rw;nSolveS. rw nLt_S_rw;nSolveS.
rw nLeq_rw;nSolveS. exists n. ee. am. rw nPlus_S_l;nSolveS.
rw nPlus_comm. am.
ap econs_list;am. am. am. am. am.
Qed.

Lemma rev_pr : forall l, is_elist l -> forall i, inc i nNum -> forall k, inc k nNum -> 
list_length l = oS (nPlus i k) -> 
ev (rev l) i = ev l k.
Proof.
ir. uf rev.
ap rev_aux_ev_begin.
am. ap is_elist_nil. am. am. am.
Qed.

Inductive  list_of_alt : E2P :=
  | list_of_nil_alt : forall a, list_of_alt enil a
  | list_of_cons_alt : forall a l, list_of_alt l a -> forall x, inc x a -> list_of_alt (econs x l) a
.

Lemma list_of_alt_eq : list_of = list_of_alt.
Proof.
ap arrow_extensionality. intro l. ap arrow_extensionality.
ir. ap iff_eq;ir.
cp (list_of_list H). rwi elist_alt_eq H0. nin H0.
constructor. apply list_of_cons in H. ee.
apply IHis_elist_alt in H1. constructor. am. am.
rw elist_alt_eq;am.
nin H. ap nil_list_of.
ap cons_list_of. am. am.
Qed.

Lemma list_of_ind : forall (a : E) (P : EP), 
P enil -> 
(forall l, list_of l a -> P l -> forall x, inc x a -> P (econs x l)) -> 
forall l, list_of l a -> P l.
Proof.
intros a P Hnil IH.
pose (p l := list_of l a -> P l).
assert (forall l, is_elist l -> p l).
ap elist_ind;uf p;clear p;ir.
am. apply list_of_cons in H1. ee.
ap IH. am. ap H0. am. am.
am.
ir. ap H. eapply list_of_list. am.
am.
Qed.

Lemma rev_aux_length : forall l', is_elist l' -> forall l, is_elist l -> 
list_length (fold_left (fun r x => econs x r) l l') = nPlus (list_length l) (list_length l').
Proof.
intros l' Hl'. cp Hl'.
rwi elist_alt_eq H. nin H.
ir. rw fold_left_nil. rw nil_length. rw nPlus_0. tv. am.
wri elist_alt_eq H.
cp (IHis_elist_alt H). clear IHis_elist_alt.
intro l'. ir.
rw fold_left_cons. rw H0. rw econs_length. rw econs_length.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS.
ap econs_list;am. am.
Qed.

Lemma rev_length : forall l, is_elist l -> list_length (rev l) = list_length l.
Proof.
ir. uf rev. rw rev_aux_length. rw nil_length. ap nPlus_0_l.
am. am. ap is_elist_nil.
Qed.

Lemma rev_aux_list : forall l', is_elist l' -> forall l, is_elist l -> 
is_elist (fold_left (fun r x => econs x r) l l').
Proof.
pose (p l' := forall l, is_elist l -> 
is_elist (fold_left (fun r x => econs x r) l l')).
assert (forall l', is_elist l' -> p l');try am.
ap elist_ind;uf p;clear p;ir.
rw fold_left_nil. am.
rw fold_left_cons. ap H0. ap econs_list. am.
am.
Qed.

Lemma rev_list : forall l, is_elist l -> is_elist (rev l).
Proof.
ir. uf rev. ap rev_aux_list. am. ap is_elist_nil.
Qed.

Lemma rev_list_of : forall l a, list_of l a -> list_of (rev l) a.
Proof.
ir.
ap list_list_of. ap rev_list. eapply list_of_list;am.
cp (list_of_list H).
nin H. ee. assert (list_length l = x). am. subst.
rw rev_length;au.
uhg;ir.
assert (inc x nNum). cp omega_ordinal. uh H3;ee;eapply H3;am.
cp H2. wri nLt_inc_rw H4;nSolveS.
rwi nLt_S_rw H4;nSolveS. rwi nLeq_rw H4;nSolveS.
destruct H4 as [k H4]. ee.
rwi nPlus_S_l H5;nSolveS.
cp H5.
apply rev_pr in H5;nSolveS.
rw H5.
eapply trans_of_map. am. 
wr nLt_inc_rw;nSolveS. rw nLt_S_rw;nSolveS.
rw nLeq_rw;nSolveS. exists x;ee. am. rw H6. rw nPlus_comm.
symmetry. ap nPlus_S_l. am. am.
Qed.

Definition lists_of a := union (Im (fun n => map_set n a) nNum).

Lemma lists_of_rw : forall l a, inc l (lists_of a) = list_of l a.
Proof.
ir. ap iff_eq;ir.
apply union_ex in H. destruct H as [x H];ee.
Im_nin H. subst. rwi map_set_rw H0.
exists x0. ee. am. am.

nin H. ee.
apply union_inc. econstructor. ee.
ap Im_inc. am. rw map_set_rw. am.
Qed.

Import Ordinal_arith.

Definition append l l' := L (oPlus (list_length l) (list_length l')) (fun p => 
by_cases
(fun _ : inc p (list_length l) => ev l p)
(fun _ : _ => let k := choose (fun k => is_ordinal k & p = oPlus (list_length l) k) in
  ev l' k)).

Lemma append_nPlus : forall l, is_elist l -> forall l', is_elist l' -> 
append l l' = L (nPlus (list_length l) (list_length l')) (fun p => 
by_cases
(fun _ : inc p (list_length l) => ev l p)
(fun _ : _ => let k := choose (fun k => inc k nNum & p = nPlus (list_length l) k) in
  ev l' k)).
Proof.
ir.
uf append.
wr nPlus_oPlus;try am.
ap create_extensionality.
intro p;ir.
assert (inc p nNum).
eapply omega_transitiveT;[|am]. nSolveS.
apply by_cases with (inc p (list_length l));ir.
rw by_cases_if. rw by_cases_if. tv.
am. am.
rw by_cases_if_not;try am. rw by_cases_if_not;try am.
ap uneq.
set (k1 := choose (fun k : E => is_ordinal k & p = oPlus (list_length l) k)).
set (k2 := choose (fun k : E => k ∈ ω & p = nPlus (list_length l) k)).
assert (is_ordinal k1 & p = oPlus (list_length l) k1).
ap choose_pr.
rwi nPlus_oPlus H1;try am.
assert (is_ordinal (list_length l)).
ap nNum_ordinal;am.
assert (is_ordinal p). ap nNum_ordinal;am.
assert (sub (list_length l) p).
destruct (ordinal_sub_sub H4 H5).
am. rwi ordinal_sub_leq_of H6;try am.
nin H6. nin H3;am. rw H6;ap sub_refl.
apply ordinal_sub_ex in H6;try am.
ee.
assert (inc k2 nNum & p = nPlus (list_length l) k2).
ap choose_pr.
wri nLt_inc_rw H3;nSolveS. wri (leq_not_lt nLeq_to) H3;nSolveS.
rwi nLeq_rw H3;nSolveS. ee.
rwi nPlus_oPlus H7;nSolveS.
eapply oPlus_reg_r. Focus 4. rwi H5 H7;ap H7.
ap nNum_ordinal;am. am. ap nNum_ordinal;am.
Qed.

Lemma append_nil : forall l', is_elist l' -> append enil l' = l'.
Proof.
ir. rw append_nPlus.
rw nil_length. rw nPlus_0_l;nSolveS.
ap function_extensionality.
ap create_axioms. am.
rw create_domain. tv.
rw create_domain.
ir.
rw create_ev. rw by_cases_if_not. simpl.
set (k := (choose (fun k : E => k ∈ ω & x = nPlus n0 k))).
assert (inc k nNum & x = nPlus n0 k). ap choose_pr.
exists x;dj. eapply omega_transitiveT;[|am]. am.
rw nPlus_0_l;nSolveS.
ee. rw H2. rw nPlus_0_l;au.
ap emptyset_empty.
am.
ap is_elist_nil. am.
Qed.

Lemma append_cons : forall x l, is_elist l -> forall l', is_elist l' -> 
append (econs x l) l' = econs x (append l l').
Proof.
ir.
rw append_nPlus;nSolveS. rw append_nPlus;nSolveS.
rw econs_length.
uf econs. rw create_domain.
rw nPlus_S_l;nSolveS.
ap create_extensionality.
ir.
assert (inc x0 nNum). eapply omega_transitiveT;[|am].
nSolveS.
apply nNum_destruct in H2;nin H2.
subst.
rw by_cases_if. rw by_cases_if.
rw create_ev. rw by_cases_if. tv.
tv.
ap n0_inc_S;am.
tv. ap n0_inc_S;am.

nin H2;ee;subst. apply nNum_S_S_inc in H1;nSolveS.
apply by_cases with (inc x1 (list_length l));ir.
rw by_cases_if. rw by_cases_if_not.
rw create_ev. rw by_cases_if_not.
rw pred_S. rw create_ev. rw by_cases_if. tv.
am. am. am. ap oS_emptyset_neq. ap nNum_inc_S_S;am.
ap oS_emptyset_neq. ap nNum_inc_S_S;nSolveS.
rw by_cases_if_not.
rw by_cases_if_not. rw pred_S;au.
rw create_ev. rw by_cases_if_not.
wri nLt_inc_rw H3;nSolveS.
wri (leq_not_lt nLeq_to) H3;nSolveS.
rwi nLeq_rw H3;nSolveS.
destruct H3 as [z H3];ee.
set (k1 := (choose (fun k : E => k ∈ ω & oS x1 = nPlus (oS (list_length l)) k))).
set (k2 := (choose (fun k : E => k ∈ ω & x1 = nPlus (list_length l) k))).
ap uneq.
assert (inc k1 nNum & oS x1 = nPlus (oS (list_length l)) k1).
ap choose_pr. exists z;ee. am. rw nPlus_S_l;nSolveS. ap uneq;am.
assert (inc k2 nNum & x1 = nPlus (list_length l) k2).
ap choose_pr. exists z;ee. am. am.
ee.
rwi nPlus_S_l H8;nSolveS. apply oS_N_inj in H8;nSolveS.
apply nPlus_reg_l with (list_length l);nSolveS.
wr H8. am.
am. am. ap oS_emptyset_neq.
uhg;ir.
ap H3. ap nNum_S_S_inc;nSolveS.
ap econs_list;am.
Qed.

Lemma append_list : forall l, is_elist l -> forall l', is_elist l' -> is_elist (append l l').
Proof.
intros l Hl. cp Hl.
rwi elist_alt_eq H. nin H.
ir. rw append_nil. am. am.
wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. rw append_cons;au. ap econs_list. au.
Qed.

Lemma append_length : forall l, is_elist l -> forall l', is_elist l' -> 
list_length (append l l') = nPlus (list_length l) (list_length l').
Proof.
intros l Hl. cp Hl.
rwi elist_alt_eq H. nin H.
ir. rw append_nil. rw nil_length. rw nPlus_0_l;nSolveS. am.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir.
rw append_cons. rw econs_length. rw econs_length.
rw nPlus_S_l;nSolveS. ap uneq. au.
am. am.
Qed.

Lemma list_of_append : forall a l, list_of l a -> forall l', list_of l' a -> 
list_of (append l l') a.
Proof.
intros a l Hl.
cp Hl. rwi list_of_alt_eq H. nin H.
ir. rw append_nil. am. eapply list_of_list;am.

wri list_of_alt_eq H. cp (IHlist_of_alt H).
clear IHlist_of_alt.
ir. rw append_cons.
ap cons_list_of. am. au. eapply list_of_list. am.
eapply list_of_list;am.
Qed.

Lemma append_list_of : forall l, is_elist l -> forall l', is_elist l' -> 
forall a, list_of (append l l') a -> 
A (list_of l a) (list_of l' a).
Proof.
intros l Hl.
cp Hl. rwi elist_alt_eq H. nin H.
ir. rwi append_nil H0. ee. ap nil_list_of. am. am.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. rwi append_cons H2. apply list_of_cons in H2.
nin H2. apply H0 in H3. ee.
apply cons_list_of. am. am. am. am. ap append_list. am. am.
am. am.
Qed.

Lemma append_fold_left : forall l, is_elist l -> forall l', is_elist l' -> 
forall f a, fold_left f a (append l l') = fold_left f (fold_left f a l) l'.
Proof.
intros l Hl.
cp Hl. rwi elist_alt_eq H. nin H.

ir. rw append_nil. rw fold_left_nil. tv. am.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. rw append_cons. rw fold_left_cons. rw fold_left_cons. rw H0.
tv. am. am. ap append_list. am. am. am. am.
Qed.

Lemma append_ev_beg : forall l, is_elist l -> forall n, inc n (list_length l) -> 
forall l', is_elist l' -> ev (append l l') n = ev l n.
Proof.
intros l Hl.
cp Hl. rwi elist_alt_eq H. nin H.

ir. rwi nil_length H. apply emptyset_empty in H;nin H.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. rwi econs_length H1.
assert (inc n nNum). cp omega_ordinal.
uh H3;ee;eapply H3. Focus 2. am. nSolveS.
rw append_cons. apply nNum_destruct in H3.
nin H3. subst. rw econs_0. rw econs_0.
tv. am. ap append_list;am.
nin H3;ee;subst. rw econs_S. rw econs_S.
ap H0. wr nLt_inc_rw;nSolveS.
rw nLt_S_S;nSolveS. rw nLt_inc_rw;nSolveS.
am. am.
wr nLt_inc_rw;nSolveS.
rw nLt_S_S;nSolveS. rw nLt_inc_rw;nSolveS.
ap append_list;am.
rw append_length;try am.
wr nLt_inc_rw;nSolveS. wri nLt_inc_rw H1;nSolveS.
wri nLt_S_S H1;nSolveS. rwi nLt_S_rw H1;nSolveS.
rwi nLeq_rw H1;nSolveS. rw nLt_S_rw;nSolveS.
rw nLeq_rw;nSolveS.
nin H1;ee. rw H4.
exists (nPlus x1 (list_length l'));ee;nSolveS.
symmetry. ap nPlus_assoc.
am. am.
Qed.

Lemma append_ev_end : forall l, is_elist l -> forall l', is_elist l' -> 
forall n, inc n (list_length l') -> 
ev (append l l') (nPlus (list_length l) n) = ev l' n.
Proof.
intros l Hl.
cp Hl. rwi elist_alt_eq H. nin H.

ir. rw append_nil. rw nil_length. rw nPlus_0_l. tv.
eapply omega_transitiveT. am. am. am.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. rw append_cons. rw econs_length.
rw nPlus_S_l. rw econs_S. ap H0. am. am.
ap append_list;am.
rw append_length.
assert (inc n nNum). eapply omega_transitiveT;am.
wr nLt_inc_rw;nSolveS. rw nLt_S_rw;nSolveS.
wr nPlus_S;nSolveS.
wri nLt_inc_rw H2;nSolveS. rwi nLt_S_rw H2;nSolveS. 
rwi nLeq_rw H2;nSolveS.
nin H2;ee.
rw H4.
rw nLeq_rw;nSolveS. exists x0. ee.
am.
ap nPlus_assoc. am. am. am.
 eapply omega_transitiveT. am. am.
am. am.
Qed.

Lemma append_inj : forall l, is_elist l -> forall l', is_elist l' -> 
forall r, is_elist r -> forall r', is_elist r' -> list_length l = list_length r -> 
append l l' = append r r' -> A (l=r) (l'=r').
Proof.
intros l Hl.
cp Hl. rwi elist_alt_eq H. nin H.

ir.
dj.
symmetry. ap length_0_nil. am.
wr H2. ap nil_length.
subst. rwi append_nil H3. rwi append_nil H3. tv. am. am.

wri elist_alt_eq H. cp (IHis_elist_alt H). clear IHis_elist_alt.
ir. apply elist_destruct in H2. nin H2.
subst. ap False_rect. rwi econs_length H4. rwi nil_length H4.
eapply oS_emptyset_neq;am.

nin H2;nin H2;nin H2;subst.
rwi econs_length H4;rwi econs_length H4.
apply oS_N_inj in H4.
rwi append_cons H5. rwi append_cons H5.
apply econs_inj in H5.
nin H5;subst.
apply H0 in H6. ee;subst.
tv. tv. am. am. am. am.
ap append_list;am. ap append_list;am. am.
am. am. am. am.
Qed.

Lemma append_inj_end : forall l, is_elist l -> forall l', is_elist l' -> 
forall r, is_elist r -> forall r', is_elist r' -> list_length l' = list_length r' -> 
append l l' = append r r' -> A (l=r) (l'=r').
Proof.
ir. ap append_inj;try am.
cp (uneq list_length H4).
rwi append_length H5. rwi append_length H5.
rwi H3 H5. apply nPlus_reg_r in H5.
am.
am. am. am. am. am. am. am.
Qed.

Lemma append_nil_end : forall l, is_elist l -> append l enil = l.
Proof.
ap elist_ind.
ap append_nil. ap is_elist_nil.
ir.
rw append_cons. ap uneq. am.
am. ap is_elist_nil.
Qed.

Lemma append_cons_end : forall l, is_elist l -> forall x l', is_elist l' -> 
append l (econs x l') = append (append l (econs x enil)) l'.
Proof.
pose (p l := forall x l' : E,
is_elist l' -> append l (econs x l') = append (append l (econs x enil)) l').
assert (forall l, is_elist l -> p l);try am.
ap elist_ind;uf p;clear p;ir.
rw append_nil. rw append_nil.
rw append_cons. rw append_nil. tv. am.
ap is_elist_nil. am. ap econs_list. ap is_elist_nil.
 ap econs_list. am.

rw append_cons. rw H0.
rw append_cons. rw append_cons. tv.
ap append_list. am. ap econs_list. ap is_elist_nil.
am. am. ap econs_list;ap is_elist_nil. am. am.
ap econs_list;am.
Qed.

Lemma append_assoc : forall l, is_elist l -> forall l', is_elist l' -> forall l'', is_elist l'' -> 
append l (append l' l'') = append (append l l') l''.
Proof.
pose (p l := forall l', is_elist l' -> forall l'' : E, is_elist l'' ->
 append l (append l' l'') = append (append l l') l'').
assert (forall l, is_elist l -> p l);try am.
ap elist_ind;uf p;clear p;ir.
rw append_nil. rw append_nil.
tv. am. ap append_list;am.
rw append_cons. rw append_cons.
rw append_cons. rw H0. tv. am. am.
ap append_list. am. am. am. am. am. am.
ap append_list;am.
Qed.

Require Import List.

Fixpoint mk_elist l := match l with
  | x::tl => econs x (mk_elist tl)
  | nil => enil
  end.

Lemma elist_of_list : forall l, is_elist (mk_elist l).
Proof.
ir;nin l;simpl.
ap is_elist_nil.
ap econs_list. am.
Qed.

Lemma mk_append : forall l l', mk_elist (l ++ l') = append (mk_elist l) (mk_elist l').
Proof.
intro l. nin l;ir.
simpl. rw append_nil. tv.
ap elist_of_list.
simpl. rw IHl. rw append_cons. tv.
ap elist_of_list. ap elist_of_list.
Qed.

Lemma mk_list_of : forall a l, (forall x, In x l -> inc x a) -> list_of (mk_elist l) a.
Proof.
ir. nin l.
simpl. ap nil_list_of.
simpl. ap cons_list_of.
ap H. simpl. au.
ap IHl. ir.
ap H. simpl. au.
Qed.

Definition list_inv : E -> list E.
ap elist_rec.
exact nil.
intros tl rtl x.
ap cons. exact x. exact rtl.
ir. exact nil.
Defined.

Lemma list_inv_nil : list_inv enil = nil.
Proof.
ap elist_rec_nil.
Qed.

Lemma list_inv_cons : forall x l, is_elist l -> 
list_inv (econs x l) = x::(list_inv l).
Proof.
ir. uf list_inv. rw elist_rec_cons. ap uneq.
tv. am.
Qed.

Lemma list_inv_l : forall l, list_inv (mk_elist l) = l.
Proof.
ir;nin l.
simpl. ap list_inv_nil.
simpl. rw list_inv_cons. ap uneq. am.
ap elist_of_list.
Qed.

Lemma list_inv_r : forall l, is_elist l -> mk_elist (list_inv l) = l.
Proof.
ap elist_ind.
rw list_inv_nil. tv.

ir. rw list_inv_cons. simpl. rw H0. tv.
am.
Qed.

Lemma list_inv_app : forall l, is_elist l -> forall l', is_elist l' -> 
list_inv (append l l') = (list_inv l)++(list_inv l').
Proof.
pose (p l := 
forall l' : E,
is_elist l' -> list_inv (append l l') = list_inv l ++ list_inv l').
assert (forall l, is_elist l -> p l);try am.
ap elist_ind;uf p;clear p;ir.
rw append_nil. rw list_inv_nil. simpl. tv. am.
rw append_cons. rw list_inv_cons. rw H0.
rw list_inv_cons. simpl. tv. am. am. ap append_list;am.
am. am.
Qed.

Ltac lSolve := match goal with
  | |- is_elist enil => ap is_elist_nil
  | |- is_elist (econs _ _) => ap econs_list;lSolve
  | |- is_elist (tail _) => ap tail_list;lSolve
  | |- is_elist (append _ _) => ap append_list;lSolve
  | _ => tv
  end.

End EList.

Require Import Permutation.

Module EPermutation.

Section NotaSec.

Notation invImg := inverse_image.

Definition perm_card f f' := axioms f & axioms f' &
forall y, card (inverse_image (singleton y) f) = card (inverse_image (singleton y) f').

Definition perm_bij_v f f' g := axioms f & axioms f' & 
bijective (domain g) (domain f) g &
f' = compose f g.

Definition perm_bij f f' := ex (perm_bij_v f f').

Lemma trans_perm_bij : forall f, axioms f -> forall f', axioms f' -> 
forall g a, perm_bij_v f f' (L a g) = (Application.bijective a (domain f) g & 
domain f' = a &
forall x, inc x a -> ev f' x = ev f (g x)).
Proof.
ir;ap iff_eq;ir.
uh H1;ee. 
rwi create_domain H3.
cp (bijective_of_map H3).
uhg;ee. uhg;ir.
cp H6;apply H5 in H7. rwi create_ev H7;am.
uhg;ir.
ap H5. am. am.
rw create_ev;try am. rw create_ev;try am.
uhg;ir.
apply H5 in H6. nin H6;ee.
exists x;ee. am. wr H7. rw create_ev;au.
rw H4. rw composable_domain.
ap create_domain.
eapply map_composable. Focus 2. ap axioms_map.
am.
am.
ir.
rw H4. rw compose_ev.
ap uneq;ap create_ev;am.
rw composable_domain.
rw create_domain;am.
eapply map_composable. Focus 2. ap axioms_map.
am.
am.
ee.
uhg;ir.
ee. am. am.
rw create_domain. ap map_of_bijective. am.
ap function_extensionality.
am. ap compose_axioms.
rw composable_domain.
rw create_domain;am.
eapply map_composable. Focus 2. ap axioms_map.
am.
ap map_of_bijective. am.
ir. rwi H2 H4.
rw compose_ev.
rw create_ev;au.
rw composable_domain. rw create_domain;am.
eapply map_composable. Focus 2. ap axioms_map.
am.
ap map_of_bijective. am.
Qed.

Lemma perm_card_equi : forall f, axioms f -> forall f', axioms f' -> 
perm_card f f' = 
(forall y, are_equipotent (inverse_image (singleton y) f) 
                                      (inverse_image (singleton y) f')).
Proof.
ir;ap iff_eq;ir;try uhg;ee;try am.
uh H1;ee.
ap card_eq_iso. au.
ir.
ap card_invariant. au.
Qed.

Definition perm_equi f f' g := axioms f & axioms f' &
forall y, bijective (invImg (singleton y) f) (invImg (singleton y) f') (g y).

Lemma perm_card_equi_v : forall f f', perm_card f f' = ex (perm_equi f f').
Proof.
ir;ap iff_eq;ir.
cp H;rwi perm_card_equi H;try am.
exists (fun y => choose (bijective (invImg (singleton y) f) (invImg (singleton y) f'))).
uhg;ee;try am.
ir. ap choose_pr. au.
nin H;uh H;ee.
rw perm_card_equi;try am.
ir;exists (x y);au.
Qed.

Lemma perm_card_sym : forall f f', perm_card f f' -> perm_card f' f.
Proof.
uf perm_card;ir;ee;au.
Qed.

Lemma perm_card_Im_eq : forall f f', perm_card f f' -> range f = range f'.
Proof.
assert (forall f f', perm_card f f' -> sub (range f) (range f')).
ir.
cp H;uh H;rwi perm_card_equi_v H0. ee.
nin H0;uh H0;ee.
uhg;ir.
apply range_ex in H5;try am. nin H5. ee.
assert (inc x0 (invImg (singleton a) f)).
ap Z_inc. am.
wr H6;ap singleton_inc.
apply (bijective_of_map (H4 a)) in H7.
apply Z_all in H7. ee.
apply singleton_eq in H8.
wr H8. apply range_ev_inc. am. am.
ir;ap extensionality;ap H. am.
ap perm_card_sym;am.
Qed.

Lemma perm_card_refl : forall f, axioms f -> perm_card f f.
Proof.
ir;uhg;ee;au.
Qed.

Lemma Im_card_inv : forall f, axioms f -> 
forall y, inc y (range f) = sub n1 (card (invImg (singleton y) f)).
Proof.
ir.
ap iff_eq;ir. wr nonempty_card.
apply range_ex in H0;try am.
nin H0;ee;subst. exists x;ap Z_inc.
am.
ap singleton_inc.
wri nonempty_card H0. nin H0.
apply Z_all in H0. ee.
apply singleton_eq in H1;subst. ap range_ev_inc.
am. am.
Qed.

Lemma perm_bij_card_v : forall f f' g, perm_bij_v f f' g -> perm_equi f f' 
(fun y => L (invImg (singleton y) f) (ev (inverse g))).
Proof.
ir. uh H;ee.
subst. assert (composable f g).
uhg;ee;am.
cp (bijective_inverse_bijective H1).
cp (bijective_inverse_of H1).
uhg;ee;try am.
ir. ap map_of_bijective.
uhg;ee;uhg;ir.
apply Z_all in H5;ee. apply singleton_eq in H6;subst.
ap Z_inc. rw composable_domain;try am. 
ap (bijective_of_map H3). am.
eapply eq_ind. ap singleton_inc. ap uneq.
rw compose_ev. uh H4;ee. uh H7;ee. ap uneq.
au.
rw composable_domain;au. ap (bijective_of_map H3);am.
apply Z_sub in H5;apply Z_sub in H6;ap H3;am.
apply Z_all in H5;ee.
rwi compose_ev H6;try am. rwi composable_domain H5;try am.
apply singleton_eq in H6;subst.
cp H5. apply H3 in H6. nin H6;ee;subst.
econstructor;ee. ap Z_inc. am.
eapply eq_ind. ap singleton_inc. ap uneq.
ap uneq. symmetry;ap H4. am.
tv.
Qed.

Lemma perm_bij_card : forall f f', perm_bij f f' -> perm_card f f'.
Proof.
ir. nin H. apply perm_bij_card_v in H.
rw perm_card_equi_v. econstructor;am.
Qed.

Lemma perm_card_trans : forall f f', perm_card f f' -> forall f'', perm_card f' f'' -> 
perm_card f f''.
Proof.
uf perm_card;ir;ee;try am.
ir. etransitivity;au.
Qed.

Lemma perm_card_v_domain : forall f f' g, perm_equi f f' g -> 
bijective (domain f) (domain f') (union (Im g (range f))).
Proof.
ir.
assert (range f = range f').
ap perm_card_Im_eq. rw perm_card_equi_v. econstructor;am.

assert (domain f = union (Im (fun y => invImg (singleton y) f) (range f))).
ap extensionality;uhg;ir.
ap union_inc;econstructor;ee.
ap Im_inc;ee.
ap range_ev_inc. am. am.
ap Z_inc. am. ap singleton_inc.
union_nin H1;Im_nin H1;subst.
apply Z_sub in H2.
am.
assert (domain f' = union (Im (fun y => invImg (singleton y) f') (range f'))).
ap extensionality;uhg;ir.
ap union_inc;econstructor;ee.
ap Im_inc;ee.
ap range_ev_inc. am. am.
ap Z_inc. am. ap singleton_inc.
union_nin H2;Im_nin H2;subst.
apply Z_sub in H3.
am.
rw H2. wr H0. rw H1. ap union_Im_bijective.
ir.
apply Z_all in H5;apply Z_all in H6;ee.
apply singleton_eq in H8;apply singleton_eq in H7;subst;tv.
ir.
apply Z_all in H5;apply Z_all in H6;ee.
apply singleton_eq in H8;apply singleton_eq in H7;subst;tv.
ir.
uh H;ee.
ap H5.
Qed.

Lemma perm_card_v_ev : forall f f' g, perm_equi f f' g -> 
forall x, inc x (domain f) -> ev f x = ev f' (ev (union (Im g (range f))) x).
Proof.
ir.
uh H;ee.
assert (inc x (invImg (singleton (ev f x)) f)).
ap Z_inc. am. ap singleton_inc.
apply (bijective_of_map (H2 (ev f x))) in H3.
apply Z_all in H3. ee.
apply singleton_eq in H4.
wr H4. ap uneq.
symmetry. ap union_ev.
ir. Im_nin H5;subst. ap H2.
rw union_strict_cond_rw. eapply (union_Im_cond_strict).
Focus 2.
ir. ap H2.
ir. simpl in *.
apply Z_all in H7;apply Z_all in H8. ee.
apply singleton_eq in H10;apply singleton_eq in H9;subst.
tv.
ap Im_inc.
ap range_ev_inc;am.
cp (H2 (ev f x)).
uh H5;ee;uh H5;ee. rw H8.
ap Z_inc. am. ap singleton_inc.
Qed.

Lemma perm_card_v_compose : forall f f' g, perm_equi f f' g -> 
f = compose f' (union (Im g (range f))).
Proof.
ir.
ap function_extensionality.
am. ap compose_axioms.
rw composable_domain.
cp (perm_card_v_domain H).
symmetry. uh H0;ee;ap H0.
cp (perm_card_v_domain H).
uhg;ee;am.
ir.
rw compose_ev. ap perm_card_v_ev.
am.
am.
cp (perm_card_v_domain H).
rw composable_domain.
eapply eq_ind. ap H0.
uh H1;ee;symmetry;ap H1.
uhg;ee;try am.
Qed.

Lemma perm_equi_bij_v : forall f f' g, perm_equi f f' g -> perm_bij_v f' f (union (Im g (range f))).
Proof.
ir.
uhg;ee. am. am.
cp (perm_card_v_domain H).
cp (match H0 with | conj A _ => match A with | conj _ A' => A' end end ).
ee. rw H1. am.
ap perm_card_v_compose. am.
Qed.

Lemma perm_equi_inverse : forall f f' g, perm_equi f f' g -> perm_equi f' f (fun y => inverse (g y)).
Proof.
ir.
uh H;ee.
uhg;ee. am. am.
ir.
cp (H1 y).
ap bijective_inverse_bijective. am.
Qed.

Lemma perm_bij_v_unicity : forall a b f, bijective a b f -> 
forall f', unicity (perm_bij_v f f').
Proof.
ir. uhg;ir.
uh H0;uh H1;ee.
subst.
cp (uneq (compose (inverse f)) H4).
rwi compose_assoc H7;try am.
rwi compose_assoc H7;try am.
rwi (bijective_inverse_compose_l H) H7.
assert (a = domain f).
symmetry. uh H;ee;ap H.
subst.
rwi bijective_rw H6;rwi surjective_range_rw H6;ee.
rwi bijective_rw H3;rwi surjective_range_rw H3;ee.
wri H11 H7.
rwi compose_id_l H7.
rwi H11 H7. wri H9 H7. rwi compose_id_l H7. tv.
am. am. ap inverse_axioms. ap inverse_axioms.
Qed.

Lemma perm_card_bij : forall f f', perm_card f f' -> perm_bij f f'.
Proof.
ir. apply perm_card_sym in H. rwi perm_card_equi_v H.
nin H. apply perm_equi_bij_v in H.
uhg. econstructor. am. 
Qed.

Export EList.

Inductive perm_list : E2P := 
  | plist_nil : perm_list enil enil
  | plist_skip : forall l l', perm_list l l' -> forall x, perm_list (econs x l) (econs x l')
  | plist_swap : forall l, is_elist l -> forall x y, perm_list (econs y (econs x l)) (econs x (econs y l))
  | plist_trans : forall l l', perm_list l l' -> forall l'', perm_list l' l'' -> perm_list l l''
.

Lemma Permutation_perm_list : forall l l', Permutation l l' -> 
perm_list (mk_elist l) (mk_elist l').
Proof.
ir. nin H;try constructor.
ap IHPermutation.
simpl. ap plist_swap.
ap elist_of_list.
eapply plist_trans;am.
Qed.

Lemma perm_list_list : forall l l', perm_list l l' -> A (is_elist l) (is_elist l').
Proof.
ir. nin H.
ee;ap is_elist_nil.
ee;ap econs_list;am.
ee;lSolve.
ee;am.
Qed.

Lemma perm_list_Permutation : forall l l', perm_list l l' ->
 Permutation (list_inv l) (list_inv l').
Proof.
ir. nin H.
rw list_inv_nil. constructor.
cp (perm_list_list H).
ee.
rw list_inv_cons;try am.
rw list_inv_cons;try am.
constructor. am.
rw list_inv_cons;lSolve.
rw list_inv_cons;lSolve.
rw list_inv_cons;lSolve.
rw list_inv_cons;lSolve.
constructor.
econstructor. am. am.
Qed.

Import Cardinal_arith.

Lemma perm_list_card : forall l l', perm_list l l' -> perm_card l l'.
Proof.
ir. ee;nin H.
uhg. ee;try am.
ap is_elist_nil. ap is_elist_nil.
ir. tv.

cp (perm_list_list H).
ee.
uhg;ee.
ap create_axioms. ap create_axioms.
ir.
apply by_cases with (x=y);ir.
subst.
replace (invImg (singleton y) (econs y l)) with (tack_on (Im oS (invImg (singleton y) l)) n0).
replace (invImg (singleton y) (econs y l')) with (tack_on (Im oS (invImg (singleton y) l')) n0).
uf tack_on.
wr Cardinal_arith.caPlus_strict_union.
wr Cardinal_arith.caPlus_strict_union.
ap Cardinal_arith.caPlus_card_proper.
eapply are_equipotent_trans.
ap are_equipotent_sym. eapply Equipotent.injects_equipotent_Im.
uhg;ir. ap oS_N_inj. am. am. 
uhg;ir. apply Z_sub in H2.
apply omega_transitiveT with (domain l);am.
eapply are_equipotent_trans. uh IHperm_list;ee. 
ap card_eq_iso. ap H4.
eapply Equipotent.injects_equipotent_Im.
uhg;ir. ap oS_N_inj;am.
uhg;ir. apply Z_sub in H2.
apply omega_transitiveT with (domain l');am.
ap are_equipotent_refl.

ap empty_emptyset;ir. apply inter2_and in H2;ee.
 apply singleton_eq in H3;subst.
Im_nin H2. symmetry in H3;eapply oS_emptyset_neq;am.
ap empty_emptyset;ir. apply inter2_and in H2;ee.
 apply singleton_eq in H3;subst.
Im_nin H2. symmetry in H3;eapply oS_emptyset_neq;am.

ap extensionality;uhg;ir.
rwi tack_on_inc H2;nin H2.
Im_nin H2. subst.
apply Z_all in H2. ee.
apply singleton_eq in H3;subst.
ap Z_inc. rw econs_length.
ap nNum_inc_S_S. am. am.
rw econs_S. ap singleton_inc.
am.
am.
subst. ap Z_inc. rw econs_length.
ap n0_inc_S. am.
rw econs_0. ap singleton_inc.
am.
apply Z_all in H2;ee.
apply singleton_eq in H3.
rwi econs_length H2.
assert (inc a nNum).
 apply omega_transitiveT with (oS (list_length l'));nSolveS.
apply nNum_destruct in H4;nin H4.
rw H4. rw tack_on_inc;au.
nin H4;ee.
rwi H5 H3. rwi econs_S H3. subst.
apply nNum_S_S_inc in H2;try am.
rw tack_on_inc;left. ap Im_inc. ap Z_inc. am.
ap singleton_inc.
am. clear H3;subst.
ap nNum_S_S_inc;am.

ap extensionality;uhg;ir.
rwi tack_on_inc H2;nin H2.
Im_nin H2. subst.
apply Z_all in H2. ee.
apply singleton_eq in H3;subst.
ap Z_inc. rw econs_length.
ap nNum_inc_S_S. am. am.
rw econs_S. ap singleton_inc.
am.
am.
subst. ap Z_inc. rw econs_length.
ap n0_inc_S. am.
rw econs_0. ap singleton_inc.
am.
apply Z_all in H2;ee.
apply singleton_eq in H3.
rwi econs_length H2.
assert (inc a nNum).
 apply omega_transitiveT with (oS (list_length l));nSolveS.
apply nNum_destruct in H4;nin H4.
rw H4. rw tack_on_inc;au.
nin H4;ee.
rwi H5 H3. rwi econs_S H3. subst.
apply nNum_S_S_inc in H2;try am.
rw tack_on_inc;left. ap Im_inc. ap Z_inc. am.
ap singleton_inc.
am. clear H3;subst.
ap nNum_S_S_inc;am.

etransitivity. etransitivity. Focus 2.
uh IHperm_list;ee. apply (H5 y).
transitivity (card (Im oS (invImg (singleton y) l))).
ap uneq.
ap extensionality;uhg;ir.
apply Z_all in H3;ee.
apply singleton_eq in H4;subst.
rwi econs_length H3.
assert (inc a nNum).
 apply omega_transitiveT with (oS (list_length l));nSolveS.
apply nNum_destruct in H4;nin H4.
subst.
nin H2. symmetry. ap econs_0;am.
nin H4;ee;subst.
apply nNum_S_S_inc in H3;try am.
ap Im_inc. ap Z_inc. am. rw econs_S. ap singleton_inc.
am. am.
Im_nin H3;subst.
apply Z_all in H3;ee. apply singleton_eq in H4;subst.
ap Z_inc. rw econs_length;ap nNum_inc_S_S;am.
rw econs_S. ap singleton_inc.
am. am.

symmetry. ap card_invariant.
eapply Equipotent.injects_equipotent_Im;try ap sub_refl.
uhg;ir.
apply Z_sub in H3;apply Z_sub in H4.
ap oS_N_inj;try am;eapply omega_transitiveT;
try ap H3;try ap H4;am.
ap card_invariant.
eapply eq_ind. eapply (fun a => Equipotent.injects_equipotent_Im (a:=a) (f:=oS)).
uhg;ir;ap oS_N_inj;am.
uhg;ir. apply Z_sub in H3. eapply omega_transitiveT;am.
ap extensionality;uhg;ir.
Im_nin H3. subst.
apply Z_all in H3;ee.
ap Z_inc. rw econs_length. ap nNum_inc_S_S;am.
rw econs_S. am.
am. am.
apply Z_all in H3;ee;subst.
rwi econs_length H3.
assert (inc a nNum).
apply omega_transitiveT with (oS (list_length l')). nSolveS. am.
apply nNum_destruct in H5. nin H5;subst.
apply singleton_eq in H4;subst.
nin H2. rw econs_0. tv. am.
nin H5;ee;subst.
apply nNum_S_S_inc in H3;try am.
ap Im_inc. ap Z_inc. am.
rwi econs_S H4;au.

ap perm_bij_card.
uhg. exists (L (oS (oS (list_length l))) (fun n => by_cases 
(fun _ : n=n0 => n1)
(fun _ : _ => by_cases
(fun _ : n=n1 => n0)
(fun _ : _ => n)))).
uhg. ee.
ap create_axioms. ap create_axioms.
rw create_domain.
ap map_of_bijective.

assert (forall x, inc x (oS (oS (list_length l))) -> 
(x = n0 \/ x = n1 \/ (exists k, x = oS (oS k) & inc k (list_length l) & inc k nNum & x<>n0 & x<>n1))).
ir.
assert (inc x0 nNum). eapply omega_transitiveT.
ap oS_nNum. ap oS_nNum. ap H.
am.
apply nNum_destruct in H1;nin H1.
subst. au.
nin H1;ee. subst. apply nNum_destruct in H1;nin H1.
subst. au.
nin H1;ee;subst.
right;right.
exists x0;ee. tv.
ap nNum_S_S_inc;nSolveS. ap nNum_S_S_inc;nSolveS.
am. ap oS_emptyset_neq.
uhg;ir.
eapply oS_emptyset_neq. ap oS_N_inj. Focus 2. ap H2. 
nSolveS.

uhg;ee;uhg;ir.
apply H0 in H1;nin H1.
subst. rw by_cases_if. rw econs_length. rw econs_length.
ap nNum_inc_S_S. nSolveS. 
ap n0_inc_S. am.
tv.
nin H1. subst.
rw by_cases_if_not. rw by_cases_if.
rw econs_length. rw econs_length.
ap n0_inc_S. nSolveS.
tv.
ap oS_emptyset_neq.
nin H1;ee;subst.
rw by_cases_if_not;au. rw by_cases_if_not;au.
repeat rw econs_length.
ap nNum_inc_S_S;nSolveS. ap nNum_inc_S_S;nSolveS.

apply H0 in H1. apply H0 in H2.
nin H1;[idtac | nin H1;[idtac | nin H1]];ee;subst;(
nin H2;[idtac | first [nin H2 | nin H1];[idtac | first [nin H2 | nin H1]]]);ee;subst;tv.
rwi by_cases_if H3. rwi by_cases_if_not H3. rwi by_cases_if H3.
au.
tv. ap oS_emptyset_neq.
tv.
rwi by_cases_if H3;tv. rwi by_cases_if_not H3;nSolveS.
rwi by_cases_if_not H3;nSolveS.
nin H6;au.
rwi by_cases_if_not H3.
rwi by_cases_if H3;tv.
rwi by_cases_if H3. au. tv. ap oS_emptyset_neq.
rwi by_cases_if_not H3. rwi by_cases_if H3;tv.
rwi by_cases_if_not H3;tv. rwi by_cases_if_not H3;tv.
nin H5;au.
ap oS_emptyset_neq.
rwi by_cases_if_not H3;tv. rwi by_cases_if_not H3;tv.
rwi by_cases_if H3;tv.
nin H7;au.
rwi by_cases_if_not H3;tv. rwi by_cases_if_not H3;tv.
rwi by_cases_if_not H3. rwi by_cases_if H3.
nin H6;au. tv. ap oS_emptyset_neq.
repeat (rwi by_cases_if_not H3;tv).

rwi econs_length H1. rwi econs_length H1.
apply H0 in H1.
nin H1. subst. exists n1. ee.
ap nNum_inc_S_S. nSolveS. ap n0_inc_S. am.
rw by_cases_if_not. rw by_cases_if;tv.
ap oS_emptyset_neq.
nin H1;ee;subst.
exists n0;ee. ap n0_inc_S. nSolveS.
rw by_cases_if;tv.
nin H1;ee;subst.
exists (oS (oS x0));ee. 
ap nNum_inc_S_S;nSolveS. ap nNum_inc_S_S;nSolveS.
rw by_cases_if_not;au.
rw by_cases_if_not;au.

assert (composable  (econs y (econs x l))
  (L (oS (oS (list_length l)))
     (fun n : E =>
      by_cases (fun _ : n = n0 => n1)
        (fun _ : n <> n0 =>
         by_cases (fun _ : n = n1 => n0) (fun _ : n <> n1 => n))))).
uhg;ee. ap create_axioms. ap create_axioms.
rw create_range.
uhg;ir.
Im_nin H0. subst.
assert (inc x0 nNum).
apply omega_transitiveT with (oS (oS (list_length l)));nSolveS.
rw econs_length. rw econs_length.
apply nNum_destruct in H1;nin H1.
subst;rw by_cases_if;tv.
ap nNum_inc_S_S;nSolveS. ap n0_inc_S. am.
nin H1;ee;subst.
rw by_cases_if_not.
apply nNum_destruct in H1;nin H1;subst.
rw by_cases_if. ap n0_inc_S;nSolveS. tv.
nin H1;ee;subst.
rw by_cases_if_not. am.
uhg;ir. apply oS_N_inj in H2;nSolveS.
apply oS_emptyset_neq in H2;am.
ap oS_emptyset_neq.

ap function_extensionality.
ap create_axioms. ap compose_axioms.
rw composable_domain. rw create_domain.
rw econs_length. rw econs_length. tv.
am.
ir.
rwi econs_length H1;rwi econs_length H1.
assert (inc x0 nNum).
apply omega_transitiveT with (oS (oS (list_length l)));nSolveS.
rw compose_ev.
Focus 2. rw composable_domain. rw create_domain. am.
am.
rw create_ev;try am.
apply nNum_destruct in H2;nin H2;subst.
rw econs_0;lSolve. 
rw by_cases_if. uf n1. rw econs_S. rw econs_0. tv. am. lSolve.
rw econs_length. ap n0_inc_S;am.
tv.
nin H2;ee;subst.
rw econs_S;lSolve.
rw by_cases_if_not.
apply nNum_destruct in H2;nin H2. subst.
rw econs_0. rw by_cases_if. rw econs_0. tv.
lSolve. tv. am.
nin H2;ee;subst.
rw econs_S. rw by_cases_if_not. rw econs_S. rw econs_S.
tv. am. ap nNum_S_S_inc;nSolveS. ap nNum_S_S_inc;nSolveS.
lSolve. rw econs_length. ap nNum_S_S_inc;nSolveS.
uhg;ir. apply oS_N_inj in H3;nSolveS.
apply oS_emptyset_neq in H3;am.
am. ap nNum_S_S_inc;nSolveS. ap nNum_S_S_inc;nSolveS.
ap oS_emptyset_neq.
rw econs_length.
ap nNum_S_S_inc;nSolveS.

apply perm_card_trans with l'. am. am.
Qed.

Lemma perm_list_Permutation_rw : forall l, is_elist l -> forall l', is_elist l' -> 
perm_list l l' = Permutation (list_inv l) (list_inv l').
Proof.
ir. ap iff_eq;ir.
ap perm_list_Permutation. am.
apply Permutation_perm_list in H1.
rwi list_inv_r H1;au. rwi list_inv_r H1;au.
Qed.

Lemma perm_list_cons_app : forall l l1, is_elist l1 -> forall l2, is_elist l2 -> 
perm_list l (append l1 l2) -> 
forall a, perm_list (econs a l) (append l1 (econs a l2)).
Proof.
ir.
cp H1.
rw perm_list_Permutation_rw;lSolve.
rwi perm_list_Permutation_rw H1;lSolve.
rw list_inv_app. rw list_inv_cons. rw list_inv_cons.
ap Permutation_cons_app. wr list_inv_app. am.
am. am. am. apply perm_list_list in H2. am.
am. lSolve.  apply perm_list_list in H2. am.
 apply perm_list_list in H2. am.
Qed.

Lemma split_around : forall l, is_elist l -> forall k, inc k (list_length l) -> 
forall x, ev l k = x -> 
exists l1, exists l2, is_elist l1 & is_elist l2 & list_length l1 = k & l = append l1 (econs x l2)
.
Proof.
ir.
exists (L k (ev l)).
cp H0.
assert (inc k nNum). eapply omega_transitiveT;am.
wri nLt_inc_rw H2;nSolveS.
rwi nLt_S_rw H2;nSolveS. rwi nLeq_rw H2;nSolveS.
destruct H2 as [z H2];ee.
exists (L z (fun p => ev l (nPlus (oS k) p))).
dj. uhg;ee. ap create_axioms. rw create_domain. am.
uhg;ee. ap create_axioms. rw create_domain. am.
ap create_domain.

ap function_extensionality.
am. ap append_list. am. lSolve.
rw append_length. rw econs_length. 
rw create_domain. rw create_domain. ufi list_length H4;
rw H4.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS.
am. lSolve.
ir.
assert (inc x0 nNum).
eapply omega_transitiveT. ap H. am.
ufi list_length H4. rwi H4 H8.
destruct ordinal_inc_eq_inc with x0 k.
ap nNum_ordinal;am. ap nNum_ordinal;am.
rw append_ev_beg. rw create_ev. tv. am. 
am. rw create_domain. am.
lSolve.
nin H10.
transitivity (ev (append (L k (ev l)) (econs x (L z (fun p : E => ev l (nPlus (oS k) p)))))
  (nPlus (list_length (L k (ev l))) n0)).
rw H10. rw H1. rw append_ev_end.
rw econs_0. tv. am. am. lSolve.
rw econs_length. rw create_domain. ap n0_inc_S;am.
rw create_domain. rw H10. ap uneq. ap nPlus_0. am.
wri nLt_inc_rw H10;nSolveS. rwi nLt_S_rw H10;nSolveS.
rwi nLeq_rw H10;nSolveS.
destruct H10 as [p H10];ee.

rw H11.
transitivity (ev
  (append (L k (ev l)) (econs x (L z (fun p0 : E => ev l (nPlus (oS k) p0)))))
  (nPlus (list_length (L k (ev l))) (oS p))).
assert (inc p z).
rwi H11 H8.
wri nLt_inc_rw H8;nSolveS. rwi nLt_S_rw H8;nSolveS.
wri nPlus_S H8;nSolveS.
apply nLeq_nPlus_reg_l in H8;nSolveS.
wr nLt_inc_rw;nSolveS. rw nLt_S_rw;nSolveS.
rw append_ev_end. rw econs_S. rw create_ev. tv.
am. am. rw create_domain. am.
am. lSolve.
rw econs_length. rw create_domain.
ap nNum_inc_S_S;nSolveS.
ap uneq.
rw create_domain.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS.
Qed.

Lemma perm_list_refl : forall l, is_elist l -> perm_list l l.
Proof.
ap elist_ind.
constructor.
constructor;am.
Qed.

Lemma perm_list_sym : forall l l', perm_list l l' -> perm_list l' l.
Proof.
ir. nin H.
constructor.
constructor. am.
constructor. am.
econstructor;am.
Qed.

Lemma perm_list_app : forall l, is_elist l -> forall l', is_elist l' -> 
forall tl, is_elist tl -> forall tl', is_elist tl' -> 
perm_list (append l tl) (append l' tl') -> 
forall a, perm_list (append l (econs a tl)) (append l' (econs a tl')).
Proof.
ir.
eapply plist_trans.
Focus 2. ap perm_list_cons_app. am. am.
ap perm_list_refl. ap append_list;am.
eapply plist_trans. Focus 2.
constructor. am.
ap perm_list_sym. ap perm_list_cons_app.
am. am. ap perm_list_refl. ap append_list;am.
Qed.

Lemma perm_list_app_inv : forall l, is_elist l -> forall l', is_elist l' -> 
forall tl, is_elist tl -> forall tl', is_elist tl' -> 
forall a, perm_list (append l (econs a tl)) (append l' (econs a tl')) -> 
perm_list (append l tl) (append l' tl').
Proof.
ir.
apply perm_list_Permutation in H3.
rw perm_list_Permutation_rw;lSolve.
rw list_inv_app;lSolve. rw list_inv_app;lSolve.
apply Permutation_app_inv with a.
rwi list_inv_app H3;lSolve. rwi list_inv_app H3;lSolve.
rwi list_inv_cons H3;lSolve. rwi list_inv_cons H3;lSolve.
Qed.

Lemma perm_card_cons_app_inv : forall l, is_elist l -> forall l1, is_elist l1 -> 
forall l2, is_elist l2 -> forall a, perm_card (econs a l) (append l1 (econs a l2)) -> 
perm_card l (append l1 l2).
Proof.
ir.
ap perm_bij_card.
apply perm_card_bij in H2.
destruct H2 as [f H2]. uh H2;ee.
assert (composable (econs a l) f).
uhg;ee. am. am. am.
cp (composable_domain H6).
wri H5 H7.
assert (is_elist (append l1 (econs a l2))).
ap append_list;lSolve.
uh H8;ee. rwi H7 H9.
assert (inc (domain (econs a l)) nNum).
rw econs_length;nSolveS.
assert (domain f = domain (econs a l)).
wr (nNum_card H9). wr (nNum_card H10).
ap card_invariant. exists f;am.
rwi econs_length H11. clear H10.
clear H8.
assert (list_length l = nPlus (list_length l1) (list_length l2)).
rwi H11 H7. rwi append_length H7;lSolve.
rwi econs_length H7. rwi nPlus_S H7. ap oS_N_inj;nSolveS.
au.
am. am.
pose (g x := (*g x = y such that ev (append l1 l2) x = ev l y*)
by_cases
(fun _ : inc x (list_length l1) => by_cases
  (fun _ : ev f x = n0 => pred (ev f (list_length l1)))
  (fun _ : _ => pred (ev f x)))
(fun _ : _ => by_cases
  (fun _ : ev f (oS x) = n0 => pred (ev f (list_length l1)))
  (fun _ : _ => pred (ev f (oS x))))).
assert (forall x, inc x (list_length l) -> 
(inc (g x) (list_length l) & ev (append l1 l2) x = ev l (g x))).
ir.
assert (inc x nNum). apply omega_transitiveT with (list_length l);am.
assert (inc (list_length l1) (domain f)).
wr H7. rw append_length;lSolve. rw econs_length;lSolve.
rw nPlus_S;nSolveS. wr nPlus_S_l;nSolveS.
ap nLeq_nPlus_l;nSolveS. rw oS_inc;au.
uf g. destruct ordinal_inc_eq_inc with x (list_length l1).
ap nNum_ordinal;am. ap nNum_ordinal;am.
rw by_cases_if. apply by_cases with (ev f x = n0);ir.
rw by_cases_if.
cp H13.
apply (bijective_of_map H4) in H16. rwi econs_length H16.
assert (inc (ev f (list_length l1)) nNum).
apply omega_transitiveT with (oS (list_length l));nSolveS.
apply nNum_destruct in H17;nin H17.
ufi n0 H15;wri H15 H17.
apply H4 in H17.
rwi H17 H14. apply ordinal_not_inc_self in H14. nin H14.
ap nNum_ordinal;am.
am. rw H11. rw oS_inc;au.
nin H17;nin H17;subst.
rw H18. rw pred_S.
rwi H18 H16. ee. ap nNum_S_S_inc;nSolveS.
rw append_ev_beg.
transitivity (ev (append l1 (econs a l2)) x).
rw append_ev_beg. tv. am. am.
lSolve.
rw H5.
rw compose_ev. rw H15. rw econs_0.
transitivity (ev (econs a l) (oS x0)).
wr H18. wr compose_ev. wr H5.
replace (list_length l1) with (nPlus (list_length l1) n0).
rw append_ev_end. rw econs_0. tv.
am. am. lSolve. rw econs_length. ap n0_inc_S;am.
ap nPlus_0;am.
rw composable_domain. am.
am.
ap econs_S. am. ap nNum_S_S_inc;nSolveS.
am. rw composable_domain. 
rw H11. rw oS_inc;au.
am.
am. am. am. am. am.
rw by_cases_if_not.
assert (inc x (domain f)). rw H11. rw oS_inc;au.
apply (bijective_of_map H4) in H16.
rwi econs_length H16.
assert (inc (ev f x) nNum). 
apply omega_transitiveT with (oS (list_length l)). nSolveS. am.
apply nNum_destruct in H17;nin H17.
nin H15;am.
nin H17;nin H17.
rw H18.
rwi H18 H16. apply nNum_S_S_inc in H16;nSolveS.
rw pred_S. ee. am.
rw append_ev_beg. transitivity (ev (append l1 (econs a l2)) x).
rw append_ev_beg. tv. am. am. lSolve.
rw H5. rw compose_ev. rw H18. ap econs_S.
am. am. rw composable_domain. rw H11. rw oS_inc;au. am.
am. am. am. am. am. am.

assert (nLeq (list_length l1) x).
nin H14. rw H14;ap sub_refl.
wri nLt_inc_rw H14;nSolveS. am.
clear H14.
rwi nLeq_rw H15;nSolveS.
destruct H15 as [z H14];nin H14.
subst.
rw by_cases_if_not.
assert (inc  (oS (nPlus (list_length l1) z)) (domain f)).
rw H11. ap nNum_inc_S_S;try am;nSolveS.
apply (bijective_of_map H4) in H15.
rwi econs_length H15.
assert (inc (ev f (oS (nPlus (list_length l1) z))) nNum).
eapply omega_transitiveT;[idtac | am]. nSolveS.
cp H10.
rwi H8 H17.
assert (inc z (list_length l2));[idtac | clear H17].
wri nLt_inc_rw H17;nSolveS. wr nLt_inc_rw;nSolveS.
rw nLt_S_rw;nSolveS. rwi nLt_S_rw H17;nSolveS.
apply nLeq_nPlus_reg_l with (list_length l1);nSolveS.
rw nPlus_S;nSolveS.
rw append_ev_end;try am.
replace (ev l2 z) with (ev (append l1 (econs a l2)) (nPlus (list_length l1) (oS z))).
rw H5. rw compose_ev.
apply nNum_destruct in H16;nin H16.
rw H16. rw by_cases_if;tv.
cp H13. apply (bijective_of_map H4) in H17.
rwi econs_length H17.
assert (inc (ev f (list_length l1)) nNum).
eapply omega_transitiveT;[idtac | am]. nSolveS.
apply nNum_destruct in H19;nin H19.
wri H16 H19.
apply H4 in H19.
assert (inc (list_length l1)  (oS (nPlus (list_length l1) z))).
wr nPlus_S_l;nSolveS. ap nLeq_nPlus_l;nSolveS. rw oS_inc;au.
wri H19 H20. apply ordinal_not_inc_self in H20;try ap nNum_ordinal;try am.
nin H20.
rw H11. rw H8. wr nPlus_S_l;nSolveS.
ap nLeq_nPlus_l;nSolveS. rw oS_inc;au.
rw H11. ap nNum_inc_S_S;nSolveS.
nin H19;nin H19.
rw H20. rw pred_S. rwi H20 H17. apply nNum_S_S_inc in H17;nSolveS.
ee. am.
rw nPlus_S;nSolveS. rw H16. rw econs_0.
transitivity (ev (econs a l) (oS x)). wr H20.
wr compose_ev. wr H5. replace (list_length l1) with (nPlus (list_length l1) n0).
rw append_ev_end. rw econs_0. tv.
am. am. lSolve. rw econs_length;ap n0_inc_S;nSolveS.
ap nPlus_0;am.
rw composable_domain. rw H11;rw H8.
wr nPlus_S_l;nSolveS. ap nLeq_nPlus_l;nSolveS. rw oS_inc;au.
am. ap econs_S;am.
am. am.
nin H16;nin H16.
rw H17.
rw by_cases_if_not.
rw pred_S.
rwi H17 H15. apply nNum_S_S_inc in H15;nSolveS.
ee. am.
rw nPlus_S;nSolveS. rw H17. ap econs_S. am. am. am.
ap oS_emptyset_neq.
rw composable_domain;try am.
rw H11. rw nPlus_S;nSolveS. ap nNum_inc_S_S;nSolveS.
rw append_ev_end. ap econs_S. am. am.
am. lSolve. rw econs_length;ap nNum_inc_S_S;am.
wr nLt_inc_rw;nSolveS. wr (leq_not_lt nLeq_to).
ap nLeq_nPlus_l;nSolveS.
am. nSolveS.

uhg;uf perm_bij_v.
exists (L (list_length l) g). ee. am. ap append_list;am.
rw create_domain.
ap map_of_bijective. ap Finite.finite_surj_bij_trans.
ap Finite.nNum_finite. am.
uhg;ee.
uhg;ir;ap H10;am.
uhg;ir.
uf g.
assert (inc (oS y) (domain (econs a l))).
rw econs_length. ap nNum_inc_S_S;am.
apply H4 in H13.
destruct H13 as [x0 H13];ee.
rwi H11 H13.
assert (inc x0 nNum & inc y nNum).
ee;eapply omega_transitiveT;[idtac | am | idtac | am];nSolveS.
nSolveS.
ee.
(*
we want x | ev (append l1 l2) x = ev l y
= ev (econs a l) (oS y) = ev (econs a l) (ev f x0)
= ev (append l1 (econs a l2)) x0
*)
destruct ordinal_inc_eq_inc with x0 (list_length l1).
ap nNum_ordinal;am. ap nNum_ordinal;am.
(*
then if x0 < length l1 -> x=x0
*)
exists x0;ee. ufi list_length H8;rw H8.
ap nLeq_nPlus_l;nSolveS.
rw by_cases_if.
rw H14. rw by_cases_if_not. ap pred_S. am.
ap oS_emptyset_neq. am.
nin H17.
(*
x0 = length l1 
*) subst. rw H14. rw pred_S;try am.
assert (inc n0 (domain (econs a l))).
rw econs_length. ap n0_inc_S;am.
apply H4 in H17. nin H17;ee.
assert (inc x nNum). eapply omega_transitiveT;[idtac | am].
rw H11. nSolveS.
apply by_cases with (inc x (list_length l1));ir.
exists x. ee. ufi list_length H8;rw H8.
ap nLeq_nPlus_l;nSolveS.
rw by_cases_if. rw by_cases_if. tv. am. am.
apply nNum_destruct in H19;nin H19.
subst.
assert (list_length l1 = n0).
apply nNum_destruct in H15;nin H15. am.
nin H15;ee;subst.
rwi H19 H20. nin H20. ap n0_inc_S;am.
rwi H19 H14. ufi n0 H14. rwi H14 H18.
apply oS_emptyset_neq in H18;nin H18.
nin H19;ee. subst.
apply by_cases with (inc x0 (list_length l1));ir.
assert (oS x0 = list_length l1).
wri nLt_inc_rw H20;nSolveS. wri (leq_not_lt nLeq_to) H20;nSolveS.
wri nLt_inc_rw H21;nSolveS. rwi nLt_S_rw H21;nSolveS.
ap extensionality;am.
wri H22 H14. rwi H14 H18. apply oS_emptyset_neq in H18;nin H18.
exists x0;ee.
ap nNum_S_S_inc;nSolveS. ufi list_length H11;wr H11. am.
rw by_cases_if_not. rw by_cases_if. tv.
am. am.
(*
x0 > length l1 -> x = pred x0
*)
apply nNum_destruct in H15;nin H15.
subst. apply emptyset_empty in H17;nin H17.
nin H15;ee;subst.
exists x;ee. ap nNum_S_S_inc;nSolveS.
rw H14. rw pred_S;try am.
rw by_cases_if_not. rw by_cases_if_not. tv.
ap oS_emptyset_neq.
rwi oS_inc H17;nin H17. uhg;ap ordinal_inc_inc_not.
ap nNum_ordinal;am. am. rw H17;ap ordinal_not_inc_self.
ap nNum_ordinal;am.

assert (composable l (L (list_length l) g)).
uhg;ee. am. ap create_axioms.
rw create_range. uhg;ir.
Im_nin H12;subst. ap H10;am.
ap function_extensionality.
ap append_list;am. ap compose_axioms.
rw append_length. rw composable_domain. rw create_domain.
au. am. am. am.
ir.
rwi append_length H13;try am. wri H8 H13.
rw compose_ev. rw create_ev. ap H10. am.
am. rw composable_domain. rw create_domain;am.
am.
Qed.

Lemma perm_card_perm_list : forall l, is_elist l -> forall l', is_elist l' -> 
perm_card l l' -> perm_list l l'.
Proof.
ap (elist_ind (P := fun l => forall l' : E, is_elist l' -> perm_card l l' -> perm_list l l')).
ir.
assert (l' = enil).
apply elist_destruct in H. nin H.
am.
nin H;nin H;ee;subst.
uh H0;ee.
cp (H2 x). clear H2.
apply card_eq_iso in H3. nin H3.
assert (inc n0 (invImg (singleton x) (econs x x0))).
ap Z_inc. rw econs_length. ap n0_inc_S;am.
rw econs_0. ap singleton_inc. am.
apply H2 in H3. nin H3;ee.
apply Z_sub in H3. ufi enil H3;rwi emptyset_domain H3.
apply emptyset_empty in H3;nin H3.
subst. constructor.

ir.
assert (exists k, inc k (list_length l') & ev l' k = x).
uh H2;ee.
cp (H4 x). clear H4. apply card_eq_iso in H5.
assert (inc n0 (invImg (singleton x) (econs x l))).
ap Z_inc. rw econs_length;ap n0_inc_S;am.
rw econs_0;try am. ap singleton_inc.
nin H5. apply (bijective_of_map H5) in H4.
apply Z_all in H4. ee.
apply singleton_eq in H6. econstructor;ee;am.
destruct H3 as [k H3]. ee.
cp (split_around H1 H3 H4).
destruct H5 as [l1 H5]. destruct H5 as [l2 H5].
ee.
rwi H8 H2. apply perm_card_cons_app_inv in H2.
apply H0 in H2.
rw H8. ap perm_list_cons_app. am. am. am.
ap append_list;am. am. am. am.
Qed.

Lemma perm_list_list_of : forall l a, list_of l a -> 
forall l', perm_list l l' -> list_of l' a.
Proof.
ir.
cp (perm_list_list H0).
ee. apply perm_list_card in H0.
ap list_list_of. am.
uhg;ir.
uh H0;ee.
cp (H5 (ev l' x)). clear H5.
apply card_eq_iso in H6.
assert (inc x (invImg (singleton (ev l' x)) l')).
ap Z_inc. am.  ap singleton_inc.
nin H6;apply H6 in H5. nin H5;ee.
subst.
apply Z_all in H5;ee.
apply singleton_eq in H7. wr H7.
ap list_of_inc. am. am.
Qed.

End NotaSec.

End EPermutation.





Module Finite_EList.
Export EList.
Export Finite.

Lemma finite_ind_alt : forall P : EP, 
P emptyset -> 
(forall x, is_finite x -> P x -> forall y, ~ inc y x -> P (tack_on x y)) -> 
forall x, is_finite x -> P x.
Proof.
ir. nin H1.
am.
apply by_cases with (inc y x);ir.
replace (tack_on x y) with x.
am.
symmetry. ap tack_on_inc_eq. am.
ap H0. am. am. am.
Qed.


Lemma finite_ex_elist : forall x, is_finite x -> 
exists l, is_elist l & bijective (list_length l) x l.
Proof.
ap finite_ind_alt.
exists enil. ee.
ap is_elist_nil. rw nil_length.
uhg;ee.
uhg;ee. ap emptyset_axioms.
ap emptyset_domain. uf enil. rw emptyset_range.
ap sub_refl.
uhg;ir. apply emptyset_empty in H. nin H.
uhg;ir. apply emptyset_empty in H. nin H.

ir.
destruct H0 as [l H0];ee.
exists (econs y l). ee. ap econs_list. am.
rw econs_length.
ap map_of_bijective.
apply bijective_of_map in H2.
uhg;ee;uhg;ir.
assert (inc x0 nNum).
eapply omega_transitiveT. Focus 2. am.
nSolveS.
apply nNum_destruct in H4;nin H4.
subst. rw by_cases_if. rw tack_on_inc. au.
tv.
rw tack_on_inc;left.
nin H4;ee;subst.
apply nNum_S_S_inc in H3;try am.
rw by_cases_if_not. rw pred_S. ap H2. am.
am.
ap oS_emptyset_neq.

assert (inc x0 nNum & inc y0 nNum).
ee;apply omega_transitiveT with (oS (list_length l));nSolveS.
ee.
apply nNum_destruct in H6;apply nNum_destruct in H7.
nin H6;nin H7;subst.
tv.
nin H7;ee;subst.
rwi by_cases_if H5. rwi by_cases_if_not H5.
rwi pred_S H5. nin H1.
rw H5. ap H2. ap nNum_S_S_inc. am. am. am.
am.
ap oS_emptyset_neq.
tv.
nin H6;ee;subst.
rwi by_cases_if_not H5. rwi by_cases_if H5.
rwi pred_S H5. nin H1. wr H5. ap H2.
ap nNum_S_S_inc;am.
am. tv. ap oS_emptyset_neq.
nin H6;nin H7;ee;subst.
rwi by_cases_if_not H5. rwi by_cases_if_not H5.
apply nNum_S_S_inc in H4;try am.
apply nNum_S_S_inc in H3;try am.
rwi pred_S H5. rwi pred_S H5.
ap uneq. ap H2;am.
am. am.
ap oS_emptyset_neq. ap oS_emptyset_neq.

rwi tack_on_inc H3;nin H3.
cp H3. apply H2 in H4.
nin H4;ee. subst.
assert (inc x0 nNum).
eapply omega_transitiveT;am.
exists (oS x0);ee.
ap nNum_inc_S_S. am. am.
rw by_cases_if_not. rw pred_S. tv.
am. ap oS_emptyset_neq.
subst. exists n0.
ee. wr nLt_inc_rw;nSolveS.
rw nLt_S_rw;nSolveS. wr nLeq_S_S;nSolveS.
rw by_cases_if. tv. tv.
Qed.

Definition finite_list x := choose (fun l => is_elist l & bijective (list_length l) x l).

Lemma finite_list_pr : forall x, is_finite x -> 
(fun l => is_elist l & bijective (list_length l) x l) (finite_list x).
Proof.
ir. ap choose_pr. ap finite_ex_elist.
am.
Qed.

Lemma finite_list_list : forall x, is_finite x -> is_elist (finite_list x).
Proof.
ir;ap finite_list_pr;am.
Qed.

Lemma finite_list_bij : forall x, is_finite x -> 
bijective (list_length (finite_list x)) x (finite_list x).
Proof.
ir;ap finite_list_pr;am.
Qed.

End Finite_EList.
Export Finite_EList.

Module Sum.
Import EList.
Import EPermutation.

Section VarSec.

Variables (pl : E2) (g e : E).
Hypothesis (Hmon : is_monoid pl g e).

Definition lsum l := fold_right pl l e.

Lemma lsum_nil : lsum enil = e.
Proof.
ap fold_right_nil.
Qed.

Lemma lsum_cons : forall x l, is_elist l -> lsum (econs x l) = pl x (lsum l).
Proof.
ir. ap fold_right_cons. am.
Qed.

Lemma lsum_inc : forall l, list_of l g -> inc (lsum l) g.
Proof.
ir. uf lsum. eapply fold_right_inc.
ap Hmon. am. am.
Qed.

Lemma lsum_append : forall l, list_of l g -> forall l', list_of l' g ->
lsum (append l l') = pl (lsum l) (lsum l').
Proof.
pose (p l := forall l' : E, list_of l' g -> lsum (append l l') = pl (lsum l) (lsum l')).
assert (forall l, list_of l g -> p l);try am.
ap list_of_ind;uf p;ir.
rw append_nil. rw lsum_nil. symmetry. ap Hmon. ap lsum_inc. am.
eapply list_of_list. am.
cp (list_of_list H);cp (list_of_list H2).
rw append_cons. rw lsum_cons. rw lsum_cons.
assert (associative pl g). am.
rw H0. ap H5. am. ap lsum_inc. am. ap lsum_inc;am.
am. am. ap append_list. am. am. am.
am.
Qed.

Lemma lsum_perm_eq : commutative pl g -> forall l l', perm_list l l' -> 
list_of l g -> list_of l' g -> lsum l = lsum l'.
Proof.
intro Hcom.
ap (perm_list_ind (P := fun l l' =>  list_of l g -> list_of l' g -> lsum l = lsum l')).
ir. tv.
ir.
cp (perm_list_list H);ee.
rw lsum_cons. rw lsum_cons.
ap uneq. ap H0.
eapply list_of_cons. am. am.
eapply list_of_cons; am. am. am.

ir.
repeat (rw lsum_cons;lSolve).
assert (associative pl g & is_lci pl g). ee;am.
ee.
rw H2;au. rw H2;au.
ap uneq2;au. ap Hcom.
eapply list_of_cons. Focus 2. am. lSolve.
eapply list_of_cons. Focus 2. am. lSolve.
eapply list_of_cons. Focus 2. am. lSolve.
eapply list_of_cons. Focus 2. am. lSolve.
ap lsum_inc.
apply list_of_tail in H1. apply list_of_tail in H1.
rwi tail_cons H1. rwi tail_cons H1. am.
am. lSolve.
eapply list_of_cons. Focus 2. am. lSolve.
eapply list_of_cons. Focus 2. am. lSolve.
ap lsum_inc.
apply list_of_tail in H1. apply list_of_tail in H1.
rwi tail_cons H1. rwi tail_cons H1. am.
am. lSolve.

ir.
rw H0;au. ap H2.
eapply perm_list_list_of.
Focus 2. am. am. am.
eapply perm_list_list_of.
Focus 2. am. am.
Qed.

(**
itersum n m f := sum of (f i) for i from n to m
**)
Definition itersum n m f := by_cases 
(fun _ : nLeq n m => let k := choose (fun k => inc k nNum & m = nPlus n k) in
  lsum (L (oS k) (fun p => f (nPlus n p))))
(fun _ : _ => e).

Lemma itersum_lt : forall n, inc n nNum -> forall m, inc m nNum -> nLt m n -> 
forall f,
itersum n m f = e.
Proof.
ir.
rwi (lt_not_leq nLeq_to) H1;nSolveS.
uf itersum. rw by_cases_if_not. tv.
am.
Qed.

Lemma itersum_leq_rw : forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, itersum n (nPlus n k) f = lsum (L (oS k) (fun p => f (nPlus n p))).
Proof.
ir.
uf itersum. rw by_cases_if.
ap uneq.
ap uneq2;tv.
assert ((fun k0 : E => k0 ∈ ω & nPlus n k = nPlus n k0) 
(choose (fun k0 : E => k0 ∈ ω & nPlus n k = nPlus n k0))).
ap choose_pr. exists k;ee;tv.
simpl in H1;ee.
apply nPlus_reg_l in H2;nSolveS.
ap uneq;au.
rw nLeq_rw;nSolveS. exists k;ee;au.
Qed.

Lemma itersum_fun_S : forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, (L (oS (oS k)) (fun p => f (nPlus n p))) = 
econs (f n) (L (oS k) (fun p => f (nPlus (oS n) p))).
Proof.
ir. uf econs. rw create_domain.
ap create_extensionality.
ir.
assert (inc x nNum). eapply omega_transitiveT;[|am].
nSolveS.
apply nNum_destruct in H2;nin H2. subst.
rw by_cases_if. rw nPlus_0. tv. am. tv.
nin H2;ee;subst.
rw by_cases_if_not.
apply nNum_S_S_inc in H1;nSolveS.
rw create_ev. rw pred_S. rw nPlus_S;nSolveS.
rw nPlus_S_l;nSolveS. am.
rw pred_S;nSolveS. ap oS_emptyset_neq.
Qed.

Lemma itersum_fun_0 : forall n, inc n nNum -> forall f,
L (oS n0) (fun p => f (nPlus n p)) = econs (f n) enil.
Proof.
ir.
uf econs. rw nil_length.
ap create_extensionality. ir.
rwi oS_inc H0;nin H0.
apply emptyset_empty in H0;nin H0.
subst. rw nPlus_0;tv. rw by_cases_if. tv. tv.
Qed.

Lemma itersum_fun_cons : forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, L (oS k) (fun p => f (nPlus n p)) = econs (f n) (L k (fun p => f (nPlus (oS n) p))).
Proof.
ir.
apply nNum_destruct in H0;nin H0. subst.
rw itersum_fun_0. ap uneq.
symmetry. ap axioms_emptyset_eq.
ap create_axioms. ap create_domain.
am.
nin H0;ee;subst.
ap itersum_fun_S. am. am.
Qed.

Lemma itersum_fun_end : forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, L (oS k) (fun p => f (nPlus n p)) = append (L k (fun p => f (nPlus n p)))
(econs (f (nPlus n k)) enil).
Proof.
assert (forall k, inc k nNum -> forall n, inc n nNum -> 
forall f : E1,
L (oS k) (fun p : E => f (nPlus n p)) =
append (L k (fun p : E => f (nPlus n p))) (econs (f (nPlus n k)) enil)).
ap (nNum_rect (P := fun k => forall n, inc n nNum -> 
forall f : E1,
L (oS k) (fun p : E => f (nPlus n p)) =
append (L k (fun p : E => f (nPlus n p))) (econs (f (nPlus n k)) enil))).
ir.
rw create_emptyset. fold enil. rw append_nil. 
uf econs. rw nil_length.
ap create_extensionality.
ir. rwi oS_inc H0;nin H0.
apply emptyset_empty in H0;nin H0. subst.
rw by_cases_if. tv. tv. lSolve.

ir.
rw itersum_fun_S;nSolveS. symmetry.
rw itersum_fun_cons;nSolveS.
symmetry.
rw append_cons;nSolveS.
ap uneq. rw H0.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS.
nSolveS.
uhg;ee. ap create_axioms. rw create_domain;am.
lSolve.
ir;ap H;am.
Qed.

Lemma lsum_single : forall x, inc x g -> lsum (econs x enil) = x.
Proof.
ir. rw lsum_cons. rw lsum_nil.
ap Hmon. am.
ap is_elist_nil.
Qed.

Lemma itersum_fun_of : forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x (nPlus n k) -> inc (f x) g) -> 
list_of (L (oS k) (fun p => f (nPlus n p))) g.
Proof.
ir.
uf list_of. exists (oS k);ee. nSolveS.
ap map_of_trans. uhg;ir.
assert (inc x nNum).
eapply omega_transitiveT;[|am]. nSolveS.
ap H1.
nSolveS.
rw nLeq_rw;nSolveS. exists x;ee;au.

wri nLt_inc_rw H2;nSolveS. rwi nLt_S_rw H2;nSolveS.
wri nLeq_S_S H2;nSolveS.
ap nLeq_nPlus_compat;nSolveS.
Qed.

Lemma itersum_eq : forall n, inc n nNum -> 
forall f, inc (f n) g -> itersum n n f = f n.
Proof.
ir. transitivity (itersum n (nPlus n n0) f).
rw nPlus_0;nSolveS.
rw itersum_leq_rw;nSolveS.
rw itersum_fun_0. ap lsum_single. am.
am.
Qed.

Lemma itersum_S : forall n, inc n nNum -> 
forall m, inc m nNum -> nLeq (oS n) m ->
forall f, 
itersum n m f = pl (f n) (itersum (oS n) m f).
Proof.
ir.
rwi nLeq_rw H1;nSolveS.
destruct H1 as [k H1];ee;subst.
transitivity (itersum n (nPlus n (oS k)) f).
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS.
rw itersum_leq_rw;nSolveS. rw itersum_leq_rw;nSolveS.
rw itersum_fun_S;nSolveS. rw lsum_cons;nSolveS.
uhg;ee. ap create_axioms. rw create_domain;nSolveS.
Qed.

Lemma itersum_inc : forall n, inc n nNum -> 
forall m, inc m nNum -> 
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x m -> inc (f x) g) -> 
inc (itersum n m f) g.
Proof.
ir. apply by_cases with (nLeq n m);ir.
rwi nLeq_rw H2;nSolveS. destruct H2 as [k H2];ee.
subst. rw itersum_leq_rw;nSolveS. ap lsum_inc.
ap itersum_fun_of. am. am. am.
rw itersum_lt;nSolveS. am.
rw (lt_not_leq nLeq_to);nSolveS.
Qed.

Lemma itersum_S_end : forall n, inc n nNum -> 
forall m, inc m nNum -> nLeq n m -> 
forall f, (forall p, inc p nNum -> nLeq n p -> nLeq p (oS m) -> inc (f p) g) ->
itersum n (oS m) f = pl (itersum n m f) (f (oS m)).
Proof.
ir.
rwi nLeq_rw H1;nSolveS.
destruct H1 as [k H1];ee;subst.
wr nPlus_S;nSolveS. rw itersum_leq_rw;nSolveS.
rw itersum_leq_rw;nSolveS.
rw itersum_fun_end;nSolveS.
rw lsum_append. rw lsum_single. tv.
ap H2. nSolveS.
rw nLeq_rw;nSolveS. exists (oS k);ee;nSolveS.
rw nPlus_S;nSolveS.
ap itersum_fun_of. am. am.
ir. ap H2. am. am.
eapply sub_trans. am.
nSolveS.
ap cons_list_of. ap H2.
nSolveS. rw nLeq_rw;nSolveS.
exists (oS k);ee;nSolveS. rw nPlus_S;nSolveS.
ap nil_list_of.
Qed.

Lemma itersum_concat : forall n, inc n nNum -> 
forall m, inc m nNum -> nLeq n m -> forall k, inc k nNum -> 
nLeq (oS m) k -> 
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x k -> inc (f x) g) -> 
pl (itersum n m f) (itersum (oS m) k f) = itersum n k f.
Proof.
assert (forall m, inc m nNum -> 
forall n, inc n nNum -> forall k, inc k nNum -> 
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x (nPlus n (oS (nPlus m k))) -> 
inc (f x) g) -> 
pl (itersum n (nPlus n m) f) (itersum (oS (nPlus n m)) (nPlus (oS (nPlus n m)) k) f) = 
itersum n (nPlus (oS (nPlus n m)) k) f).

ap (nNum_rect (P := fun m => forall n, inc n nNum -> 
forall k : E,
(k ∈ ω) ->
forall f : E1,
(forall x : E,
 (x ∈ ω) -> nLeq n x -> nLeq x (nPlus n (oS (nPlus m k))) -> (f x ∈ g)) ->
pl (itersum n (nPlus n m) f)
  (itersum (oS (nPlus n m)) (nPlus (oS (nPlus n m)) k) f) =
itersum n (nPlus (oS (nPlus n m)) k) f)).
ir.
rw nPlus_0;nSolveS.
rw itersum_eq;nSolveS.
symmetry. rw itersum_S. tv. am.
nSolveS. rw nLeq_rw;nSolveS. exists k;ee;au.
ap H1. am. nSolveS.
rw nLeq_rw;nSolveS. econstructor;ee;try ap eq_refl. nSolveS.

ir.
replace (nPlus n2 (oS n)) with (nPlus (oS n2) n).
cp (H0 (oS n2) (oS_nNum H1)).
clear H0.
cp (H4 k H2);clear H4.
rw itersum_S;nSolveS.
symmetry. rw itersum_S;nSolveS.
symmetry.
assert (associative pl g). am.
wr H4. ap uneq.
ap H0.
ir. ap H3. am.
apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS. rw nPlus_S;nSolveS.
rwi nPlus_S_l H7;nSolveS. rwi nPlus_S H7;nSolveS.
ap H3. am. ap sub_refl.
rw nLeq_rw;nSolveS. econstructor;ee;try ap eq_refl.
nSolveS.
ap itersum_inc.
nSolveS. nSolveS.
ir.
ap H3. am. apply sub_trans with (oS n2);nSolveS.
eapply sub_trans. am.
fold nLeq. rw nLeq_rw;nSolveS.
exists (oS k);ee. nSolveS.
rw nPlus_S;nSolveS. rw nPlus_S;nSolveS.
rw nPlus_S_l;nSolveS. rw nPlus_S;nSolveS.
rw nPlus_S_l;nSolveS. rw nPlus_S_l;nSolveS.
ap uneq;ap uneq. ap nPlus_assoc.
ap itersum_inc.
nSolveS. nSolveS.
ir.
ap H3. am.
eapply sub_trans;[idtac | am].
rw nLeq_rw;nSolveS. exists (oS (oS n));ee.
nSolveS. rw nPlus_S_l;nSolveS. rw nPlus_S;nSolveS. rw nPlus_S;nSolveS.
eapply eq_ind. am.
rw nPlus_S_l;nSolveS. rw nPlus_S_l;nSolveS.
rw nPlus_S_l;nSolveS. rw nPlus_S_l;nSolveS.
rw nPlus_S;nSolveS. rw nPlus_S;nSolveS.
ap uneq;ap uneq. symmetry;ap nPlus_assoc.
rw nLeq_rw;nSolveS.
exists (oS (nPlus n k));ee. nSolveS.
repeat (rw nPlus_S;nSolveS). repeat (rw nPlus_S_l;nSolveS).
ap uneq;ap uneq. symmetry;ap nPlus_assoc.
ap nLeq_nPlus_l;nSolveS.
rw nPlus_S;nSolveS;rw nPlus_S_l;nSolveS.

ir.
rwi nLeq_rw H2;nSolveS;rwi nLeq_rw H4;nSolveS.
nin H2;ee;nin H4;ee;subst.
ap H;try am.
ir;ap H5;try am.
eapply eq_ind. am.
rw nPlus_S;nSolveS. rw nPlus_S_l;nSolveS. ap uneq.
ap nPlus_assoc.
Qed.

Lemma itersum_join : commutative pl g -> 
forall n, inc n nNum -> forall m, inc m nNum -> 
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x m -> inc (f x) g) -> 
forall h, (forall x, inc x nNum -> nLeq n x -> nLeq x m -> inc (h x) g) -> 
pl (itersum n m f) (itersum n m h) = itersum n m (fun x => pl (f x) (h x)).
Proof.
intro Hcom.
assert (forall m, inc m nNum -> forall n, inc n nNum ->
forall f, (forall x, inc x nNum -> nLeq n x -> nLeq x (nPlus n m) -> inc (f x) g) -> 
forall h, (forall x, inc x nNum -> nLeq n x -> nLeq x (nPlus n m) -> inc (h x) g) -> 
pl (itersum n (nPlus n m) f) (itersum n (nPlus n m) h) = itersum n (nPlus n m) (fun x => pl (f x) (h x))).
ap (nNum_rect (P := fun m => 
forall n : E,
(n ∈ ω) ->
forall f : E1,
(forall x : E, (x ∈ ω) -> nLeq n x -> nLeq x (nPlus n m) -> (f x ∈ g)) ->
forall h : E1,
(forall x : E, (x ∈ ω) -> nLeq n x -> nLeq x (nPlus n m) -> (h x ∈ g)) ->
pl (itersum n (nPlus n m) f) (itersum n (nPlus n m) h) =
itersum n (nPlus n m) (fun x : E => pl (f x) (h x)))).
ir. rw nPlus_0;nSolveS.
rw itersum_eq. rw itersum_eq. rw itersum_eq.
tv.
am. ap Hmon. ap H0. am. ap sub_refl. rw nPlus_0;nSolveS.
ap H1;nSolveS. rw nPlus_0;nSolveS.
am. ap H1;nSolveS. rw nPlus_0;nSolveS.
am. ap H0;nSolveS. rw nPlus_0;nSolveS.

ir.
replace (nPlus n2 (oS n)) with (nPlus (oS n2) n).
rw itersum_S;nSolveS. rw (itersum_S H1);nSolveS.
rw (itersum_S H1);nSolveS.
set (k := (itersum (oS n2) (nPlus (oS n2) n) f)).
set (k' := (itersum (oS n2) (nPlus (oS n2) n) h)).
set (k'' := (itersum (oS n2) (nPlus (oS n2) n) (fun x : E => pl (f x) (h x)))).
assert (inc k g). ap itersum_inc;nSolveS. ir.
ap H2. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS. wr nPlus_S_l;nSolveS.

assert (inc k' g).
ap itersum_inc;nSolveS. ir.
ap H3. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS. wr nPlus_S_l;nSolveS.
assert (inc k'' g).
ap itersum_inc;nSolveS. ir.
ap Hmon.
ap H2. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS. wr nPlus_S_l;nSolveS.
ap H3. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS. wr nPlus_S_l;nSolveS.
assert (k'' = pl k k').
symmetry. ap H0;nSolveS.
ir. ap H2. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS;wr nPlus_S_l;nSolveS.
ir. ap H3. am. apply sub_trans with (oS n2);nSolveS.
rw nPlus_S;nSolveS;wr nPlus_S_l;nSolveS.
rw H7.
assert (associative pl g).  am.
assert (inc (f n2) g). ap H2. am. ap sub_refl.
ap nLeq_nPlus_l;nSolveS.
assert (inc (h n2) g). ap H3;nSolveS.
ap nLeq_nPlus_l;nSolveS.
assert (is_lci pl g). am.
uh H11.
wr H8;au.  wr H8;au. ap uneq.
rw Hcom;au. wr H8;au. ap uneq. ap Hcom;am.
ap nLeq_nPlus_l;nSolveS. ap nLeq_nPlus_l;nSolveS.
ap nLeq_nPlus_l;nSolveS.
rw nPlus_S;nSolveS;rw nPlus_S_l;nSolveS.

ir.
apply by_cases with (nLeq n m);ir.
rwi nLeq_rw H4;nSolveS. nin H4;ee;subst.
ap H;am.
wri (lt_not_leq nLeq_to) H4;nSolveS.
fold nLt in H4.
rw itersum_lt;nSolveS. rw itersum_lt;nSolveS.
rw itersum_lt;nSolveS.
ap Hmon. ap Hmon.
Qed.

Lemma itersum_same : forall n, inc n nNum -> forall m, inc m nNum -> 
forall f g, (forall x, inc x nNum -> nLeq n x -> nLeq x m -> f x = g x) -> 
itersum n m f = itersum n m g.
Proof.
assert (forall m, inc m nNum -> 
forall n, inc n nNum -> 
forall f g, (forall x, inc x nNum -> nLeq n x -> nLeq x (nPlus n m) -> f x = g x) -> 
itersum n (nPlus n m) f = itersum n (nPlus n m) g).
ir.
rw itersum_leq_rw;nSolveS. rw itersum_leq_rw;nSolveS.
ap uneq. ap create_extensionality.
ir.
assert (inc x nNum). eapply omega_transitiveT;[|am]. nSolveS.
ap H1. nSolveS. ap nLeq_nPlus_l;nSolveS.
ap nLeq_nPlus_compat;nSolveS.
wri nLt_inc_rw H2;nSolveS. rwi nLt_S_rw H2;nSolveS.
rw nLeq_S_S;nSolveS.
ir.
apply by_cases with (nLeq n m);ir.
rwi nLeq_rw H3;nSolveS. nin H3. ee;subst.
ap H;am.

wri (lt_not_leq nLeq_to) H3;nSolveS. fold nLt in H3.
rw itersum_lt;nSolveS. rw itersum_lt;nSolveS.
Qed.

Section SumOver.

(*sumover : sum of the elements of a family indexed by a finite set*)
Hypothesis (Hcom : commutative pl g).

Lemma finite_family_ex_list : forall f, axioms f -> is_finite (domain f) -> 
exists l, is_elist l & perm_card f l.
Proof.
ir.
assert (inc (card (domain f)) nNum).
ap finite_card_nNum. am.
cp (card_equipotent (domain f)).
apply are_equipotent_sym in H2.
destruct H2 as [h H2].
cp (bijective_inverse_bijective H2).
pose (l := compose f h).
assert (composable f h).
uhg;ee. am. am. am.
exists l;ee. uhg;ee. ap compose_axioms.
uf l. rw composable_domain.
replace (domain h) with (card (domain f)). am.
symmetry. uh H2;ee;ap H2.
am.
ap perm_bij_card.
exists h;uhg;ee. am. ap compose_axioms.
replace (domain h) with (card (domain f)). am.
symmetry;uh H2;ee;ap H2.
tv.
Qed.

Definition sumover f := let l := choose (fun l => is_elist l & perm_card f l) in
lsum l.

Lemma sumover_pr : forall f, is_finite (domain f) -> is_map (domain f) g f -> 
forall l, is_elist l -> perm_card f l -> sumover f = lsum l.
Proof.
ir.
uf sumover.
set (l' := choose (fun l0 : E => is_elist l0 & perm_card f l0)).
assert (is_elist l' & perm_card f l'). ap choose_pr. exists l;ee;am.
ee.
ap lsum_perm_eq. am.
ap perm_card_perm_list.
am. am.
apply perm_card_trans with f. ap perm_card_sym. am.
am.
cp (perm_card_Im_eq H4).
uhg. exists (domain l');ee.
am. uhg;ee;try am. tv.
wr H5. am.
cp (perm_card_Im_eq H2).
uhg. exists (domain l);ee.
am. uhg;ee;try am. tv.
wr H5. am.
Qed.

End SumOver.

Lemma lsum_const : forall a, inc a g -> 
forall n, inc n nNum -> lsum (L n (fun _ => a)) = pow pl e a n.
Proof.
intros a Ha.
ap nNum_rect.
rw create_emptyset. fold enil;rw lsum_nil.
rw pow_0. tv.

ir.
transitivity (lsum (econs a (L n (fun _ => a)))).
ap uneq. uf econs. rw create_domain.
ap create_extensionality;ir.
assert (inc x nNum). eapply omega_transitiveT;[|am].
nSolveS.
apply nNum_destruct in H2;nin H2.
rw by_cases_if;au.
nin H2;ee;subst.
rw by_cases_if_not. rw pred_S. rw create_ev. tv.
ap nNum_S_S_inc;nSolveS. am.
ap oS_emptyset_neq.
rw lsum_cons. rw H0. symmetry.
ap pow_S. am. uhg;ee. ap create_axioms. rw create_domain;am.
Qed.

Lemma itersum_const : forall a, inc a g -> 
forall n, inc n nNum -> forall k, inc k nNum -> 
itersum n (nPlus n k) (fun _ => a) = pow pl e a (oS k).
Proof.
ir. rw itersum_leq_rw;nSolveS.
ap lsum_const.
am. nSolveS. 
Qed.

End VarSec.

Lemma sumover_const : forall pl g e, is_monoid pl g e ->
forall a, inc a g -> 
forall x, is_finite x -> 
sumover pl e (L x (fun _ => a)) = pow pl e a (card x).
Proof.
ir.
assert (inc (card x) nNum).
ap finite_card_nNum. am.
cp (lsum_const ).
wr (H3 pl g e).

assert (Commutative.is_comm_subset pl g (Engender.engendered_set pl (doubleton e a))).
ap Commutative.engenders_comm.
am. am.
ap Commutative.doubleton_comm_subset.
am. am. transitivity a.
ap H. am. symmetry;ap H;am.
uh H4;ee.
set (h :=  Engender.engendered_set pl (doubleton e a)) in *.
assert (is_monoid pl h e).
uhg;ee. ap Engender.engendered_set_lci.
uhg;ee. ap Engender.engendered_sub_initial. ap doubleton_l.
ir. ap H. ap H4. am.
ir;ap H;ap H4;am.
uhg;ir;ap H;ap H4;am.
ap (sumover_pr H6). am. rw create_domain. am.
rw create_domain. ap map_of_trans.
uhg;ir.  ap Engender.engendered_sub_initial. ap doubleton_r.
uhg;ee. ap create_axioms.
rw create_domain. am.
rw perm_card_equi;try ap create_axioms.
ir.
apply by_cases with (y=a);ir. subst.
replace (inverse_image (singleton a) (L x (fun _ : E => a))) with x.
replace (inverse_image (singleton a) (L (card x) (fun _ : E => a))) with (card x).
ap card_equipotent.
ap extensionality;uhg;ir.
ap Z_inc. rw create_domain;am.
rw create_ev. ap singleton_inc. am.
apply Z_sub in H7. rwi create_domain H7;am.
ap extensionality;uhg;ir.
ap Z_inc. rw create_domain;am.
rw create_ev. ap singleton_inc. am.
apply Z_sub in H7. rwi create_domain H7;am.
replace (inverse_image (singleton y) (L x (fun _ : E => a))) with emptyset.
replace (inverse_image (singleton y) (L (card x) (fun _ : E => a))) with emptyset.
ap are_equipotent_refl.
symmetry;ap empty_emptyset. ir.
apply Z_all in H8;ee.
rwi create_domain H8. ap H7;symmetry;apply singleton_eq in H9;
rwi create_ev H9;am.
symmetry;ap empty_emptyset. ir.
apply Z_all in H8;ee.
rwi create_domain H8. ap H7;symmetry;apply singleton_eq in H9;
rwi create_ev H9;am.
am.
am.
Qed.

End Sum.
Export Sum.

End Utils1.
Export Utils1.


