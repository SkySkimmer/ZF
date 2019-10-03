Set Implicit Arguments.
Unset Strict Implicit.

Require Export axioms.

Module Application.

Definition axioms a b f := forall x, inc x a -> inc (f x) b.

Definition injects a (f:E1) := forall x y, inc x a -> inc y a -> f x = f y -> x = y.

Definition covers a b f := forall y, inc y b -> exists x, inc x a & f x = y.

Definition injective a b f := and (axioms a b f) (injects a f).
Definition surjective a b f := and (axioms a b f) (covers a b f).
Definition bijective a b f := and (axioms a b f) (and (injects a f) (covers a b f)).

Lemma injective_surjective_back : forall a b, (exists f, injective a b f) -> 
nonempty a -> exists f, surjective b a f.
Proof.
ir. nin H0.
destruct H as [f H].
exists (fun y => by_cases 
(fun _ : (exists x, inc x a & f x = y) => unique_choose (fun x => inc x a & f x = y))
(fun _ : (~ exists x, inc x a & f x = y) => x)).
uhg;ee.
uhg;ir.
apply by_cases with (exists x1, inc x1 a & f x1 = x0);ir.
rw by_cases_if.
apply unique_choose_pr in H2. am.
uhg;ir. ee. ap H;au. rw H5;au.
am.
rw by_cases_if_not;am.

uhg;ir.
exists (f y).
ee. ap H. am.
rw by_cases_if.
assert (exists x0, inc x0 a & f x0 = f y). exists y;ee;tv.
apply unique_choose_pr in H2.
ee.
uh H;ee. apply H4 in H3.
am. am. am.
uhg;ir. ee;ap H;au. rw H5;au.

exists y;ee;tv.
Qed.

(*needs choice*)
Lemma surjective_injective_back : forall a b, (exists f, surjective a b f) -> 
exists f, injective b a f.
Proof.
ir. destruct H as [f H].

exists (fun y => choose (fun x => inc x a & f x = y)).
set (f' := fun y => choose (fun x => inc x a & f x = y)).
assert (forall y, inc y b -> (inc (f' y) a & f (f' y) = y)).
ir. uf f'. ap choose_pr.
uh H;ee. uh H1. ap H1. am.

uhg;ee. uhg;ir.
ap H0. am.

uhg;ir.
cp (H0 x H1). cp (H0 y H2).
ee.
wr H7. rw H3. am.
Qed.

Lemma cantor_strong : forall x, ~ exists f, surjective x (powerset x) f.
Proof.
ir.
uhg;ir.
destruct H as [f H].
pose (z := Z x (fun a => ~ inc a (f a))).

assert (inc z (powerset x)). ap powerset_inc. ap Z_sub.
cp H0. apply H in H1. nin H1. ee.
assert (~ inc x0 z). wr H2.
uhg;ir.
cp H3. rwi H2 H4. apply Z_all in H4;ee.
au.
ap H3. ap Z_inc. am.
rw H2. am.
Qed.

(*needs choice?*)
Lemma cantor_weak : forall x, ~ exists f, injective (powerset x) x f.
Proof.
ir;uhg;ir. apply cantor_strong with x.
ap injective_surjective_back. am.
econstructor. ap powerset_inc. ap emptyset_sub_all.
Qed.

End Application.

Module Relators.

Section Definitions.

Variables (r : E2P) (a : E).

Definition reflexiveT := forall x, inc x a -> r x x.

Definition antisymmetricT := forall x, inc x a -> forall y, inc y a -> r x y ->
 r y x -> x=y.

Definition symmetricT := forall x, inc x a -> forall y, inc y a -> r x y -> r y x.

Definition transitiveT := forall x, inc x a -> forall y, inc y a -> r x y ->
 forall z, inc z a -> r y z -> r x z.

Definition irreflexiveT := forall x, inc x a -> ~ r x x.

Definition is_order := and (reflexiveT ) (and (antisymmetricT ) (transitiveT )).

Definition is_strict_order := and (irreflexiveT ) (transitiveT ).

Definition is_total := forall x, inc x a -> forall y, inc y a -> (r x y \/ r y x).

Definition is_total_order := and (is_order) (is_total).

Definition is_equivalence := and (reflexiveT ) (and (symmetricT ) (transitiveT )).

Definition class_of x := Z a (r x).

Definition quotient := Im class_of a.

Inductive is_class : EP :=
  | class_of_class : forall x, inc x a -> is_class (class_of x).

Lemma in_quotient_is_class : forall q, inc q quotient -> is_class q.
Proof.
ir. apply Im_ex in H;nin H;ee;subst.
ap class_of_class;am.
Qed.

Lemma class_of_in_quotient : forall x, inc x a -> inc (class_of x) quotient.
Proof.
ap Im_inc.
Qed.

Lemma class_in_quotient : forall q, is_class q -> inc q quotient.
Proof.
ir. nin H. ap Im_inc. am.
Qed.

Lemma quotient_rw : quotient = Z (powerset a) (is_class).
Proof.
ap extensionality;uhg;ir.
apply Im_ex in H;nin H;ee;subst.
ap Z_inc. ap powerset_inc. ap Z_sub. ap class_of_class. am.
ap class_in_quotient. eapply Z_pr. am.
Qed.

Lemma class_of_sub : forall x, sub (class_of x) a.
Proof.
ir. ap Z_sub.
Qed.

Lemma class_sub : forall q, is_class q -> sub q a.
Proof.
ir. nin H. ap class_of_sub.
Qed.

Lemma related_classes_eq : is_equivalence -> forall x, inc x a ->
 forall y, inc y a -> r x y -> class_of x = class_of y.
Proof.
intro H.
assert (forall x, inc x a -> forall y, inc y a -> r x y -> sub (class_of x) (class_of y)).
ir. uhg;ir. apply Z_all in H3. ee.
ap Z_inc. am. uh H;ee. apply H6 with x;au. 
ir.
ap extensionality;ap H0;au.
ap H. am. am. am.
Qed.

Lemma class_of_origin : is_equivalence -> forall x, inc x a -> inc x (class_of x).
Proof.
ir;ap Z_inc;au. uh H;ee;ap H;am.
Qed.

Lemma classes_eq_related : is_equivalence -> forall x, inc x a -> forall y, inc y a -> 
class_of x = class_of y -> r x y.
Proof.
ir. eapply Z_pr.
cp (class_of_origin H H1). wri H2 H3. ap H3.
Qed.

Lemma class_nonempty : is_equivalence -> forall q, is_class q -> nonempty q.
Proof.
ir. nin H0. exists x. ap class_of_origin;am.
Qed.

Lemma class_rep_inc : is_equivalence -> forall q, is_class q -> inc (rep q) q.
Proof.
ir. ap rep_inc. ap class_nonempty;am. 
Qed.

Lemma class_of_class_of : is_equivalence -> forall x, inc x a ->
 class_of x = class_of (rep (class_of x)).
Proof.
ir.
ap related_classes_eq. am. am.
eapply class_sub. eapply class_of_class. am.
ap class_rep_inc. am. ap class_of_class;am.
cp (class_rep_inc H (class_of_class H0)).
apply Z_pr in H1. am.
Qed.

Lemma class_of_rep : is_equivalence -> forall q, is_class q -> q = class_of (rep q).
Proof.
ir. nin H0. ap class_of_class_of;am.
Qed.

Definition lt_of x y := and (r x y) (x<>y).

End Definitions.

Lemma sub_is_order : forall a, is_order sub a.
Proof.
ir;uhg;ee;uhg;ir.
ap sub_refl. ap extensionality;am.
apply sub_trans with y;am.
Qed.

Lemma eq_equivalence : forall a, is_equivalence eq a.
Proof.
ir. uhg;ee;uhg;ir.
tv.
symmetry;am.
transitivity y;am.
Qed.

End Relators. Export Relators.

Module Relation.

Definition relation r := forall x, inc x r -> is_pair x.
Definition functional r := forall x, unicity (fun y => inc (pair x y) r).

Definition domain f := Z (union (union f)) (fun x => exists y, inc (pair x y) f).

Lemma domain_inc : forall f x, (exists y, inc (pair x y) f) -> 
inc x (domain f).
Proof.
ir. ap Z_inc.
nin H.
ap union_inc.
econstructor. ee.
ap union_inc. econstructor.
ee. ap H. ap doubleton_r.
ap doubleton_l.
am.
Qed.

Lemma domain_rel_P_in : forall f, relation f -> forall x, inc x f -> 
inc (P x) (domain f).
Proof.
ir. uh H.
cp (H x H0). nin H1. clpr.
ap domain_inc. exists b;am.
Qed.

Definition range f := Im Q (Z f is_pair).

Lemma range_inc : forall f y, (exists x, inc (pair x y) f) -> inc y (range f).
Proof.
ir. nin H.
ap Im_show_inc. econstructor;ee. ap Z_inc. ap H.
ap pair_is_pair. clpr. tv.
Qed.

Definition R r x y := inc (pair x y) r.

Lemma domain_range_ex : forall r x, inc x (domain r) -> exists y, R r x y.
Proof.
ir. apply Z_pr in H.
nin H. exists x0;am.
Qed.

Lemma range_domain_ex : forall r y, inc y (range r) -> exists x, R r x y.
Proof.
ir. apply Im_ex in H. nin H. ee.
apply Z_all in H. ee. nin H1;subst.
clpr. exists a;am.
Qed.

Lemma related_domain : forall r x y, R r x y -> inc x (domain r).
Proof.
ir. ap domain_inc. exists y. am.
Qed.

Lemma related_range : forall r x y, R r x y -> inc y (range r).
Proof.
ir;ap range_inc. exists x;am.
Qed.

Lemma domain_inc_rw : forall r a, inc a (domain r) = exists b, R r a b.
Proof.
ir;ap iff_eq.
ap domain_range_ex.
ap domain_inc.
Qed.

Lemma range_inc_rw : forall r b, inc b (range r) = exists a, R r a b.
Proof.
ir;ap iff_eq.
ap range_domain_ex.
ap range_inc.
Qed.

Lemma emptyset_relation : relation emptyset.
Proof.
uhg;ir. emptyset_auto.
Qed.

Lemma relation_related : forall r, relation r -> forall p, inc p r ->
 inc (pair (P p) (Q p)) r.
Proof.
ir. cp H0;apply H in H0;nin H0. clpr. am.
Qed.

Definition reverse r := Im (fun p => if P_dec (is_pair p) 
then pair (Q p) (P p) else p) r.

Lemma pair_reverse : forall r a b, R r a b -> R (reverse r) b a.
Proof.
uf R;ir. 
ap Im_show_inc. econstructor;ee. am.
rw P_dec_if. clpr. tv.
constructor.
Qed.

Lemma reverse_pair : forall r a b, R (reverse r) a b -> R r b a.
Proof.
uf R;ir.
Im_nin H. 
nin (P_dec (is_pair x)). nin a0. clpri H0.
apply pair_eq in H0. ee;subst. am.
subst. nin b0. constructor.
Qed.

Lemma reverse_R_rw : forall r, R (reverse r) = fun a b => R r b a.
Proof.
ir. ap arrow_extensionality. ir. ap arrow_extensionality.
intro b. ap iff_eq.
ap reverse_pair. ap pair_reverse.
Qed.

Lemma not_pair_reverse : forall x, ~ (is_pair x) -> forall r, inc x r ->
 inc x (reverse r).
Proof.
ir. ap Im_show_inc. exists x;ee. am. rw P_dec_if_not. tv. am.
Qed.

Lemma reverse_not_pair : forall x, ~ (is_pair x) -> forall r, inc x (reverse r) ->
 inc x r.
Proof.
ir. Im_nin H0.
rwi P_dec_if_not H1. subst. am.
uhg;ir. rwi P_dec_if H1. subst. ap H. constructor.
am.
Qed.

Lemma reverse_reverse : forall r, reverse (reverse r) = r.
Proof.
ir;ap extensionality;uhg;ir.
apply by_cases with (is_pair a);ir.
nin H0. ap reverse_pair. ap reverse_pair. am.
ap reverse_not_pair. am. ap reverse_not_pair. am. am.
apply by_cases with (is_pair a);ir.
nin H0. ap pair_reverse. ap pair_reverse. am.
ap not_pair_reverse. am. ap not_pair_reverse. am. 
am.
Qed.

Lemma reverse_relation : forall r, relation (reverse r) = relation r.
Proof.
assert (forall r, relation (reverse r) -> relation r).
uhg;ir. ap excluded_middle;intro.
ap H1. ap H. ap Im_show_inc. exists x.
ee. am. rw P_dec_if_not. tv. am.

ir. ap iff_eq.
am.
ir. ap H. rw reverse_reverse. am.
Qed.

Definition relates r a b := sub r (product a b).

Lemma relates_relation : forall r a b, relates r a b -> relation r.
Proof.
uhg;ir.
apply H in H0. apply product_pr in H0;am.
Qed.

Lemma emptyset_relates : forall a b, relates emptyset a b.
Proof.
ir. ap emptyset_sub_all.
Qed.

Lemma product_relates : forall a b, relates (product a b) a b.
Proof.
ir;ap sub_refl.
Qed.

Lemma sub_relates : forall r a b, relates r a b -> forall r', sub r' r -> relates r' a b.
Proof.
ir;apply sub_trans with r;am.
Qed.

Lemma relates_inc_rw : forall r a b, relates r a b = inc r (powerset (product a b)).
Proof.
uf relates. ir. symmetry. ap powerset_rw.
Qed.

Lemma relates_inc : forall r a b, relates r a b -> forall x y, R r x y ->
 and (inc x a) (inc y b).
Proof.
ir. ap product_pair_pr. ap H. am.
Qed.

Lemma relates_inc_l : forall r a b, relates r a b -> forall x y, R r x y -> inc x a.
Proof.
ap relates_inc.
Qed.

Lemma relates_inc_r : forall r a b, relates r a b -> forall x y, R r x y -> inc y b.
Proof.
ap relates_inc.
Qed.

Lemma relates_reverse : forall r a b, relates r a b -> relates (reverse r) b a.
Proof.
ir. uhg;uhg;ir.
Im_nin H0. apply H in H0. apply product_pr in H0.
ee. nin H0. clpri H2;clpri H3;clpri H1.
rwi P_dec_if H1. subst. ap product_pair_inc.
am. am.
constructor.
Qed.

Lemma reverse_relates : forall r a b, relates (reverse r) a b -> relates r b a.
Proof.
ir. wr (reverse_reverse r).
ap relates_reverse. am.
Qed.

Definition superrel r := product (union2 (domain r) (range r))
                                                  (union2 (domain r) (range r)).

Lemma superrel_sub : forall r, relation r -> sub r (superrel r).
Proof.
uhg;ir. cp H0;apply H in H0. nin H0.
ap product_pair_inc.
ap union2_l;eapply domain_inc. exists b;am.
ap union2_r;eapply range_inc. exists a;am.
Qed.

Lemma product_relation : forall a b, relation (product a b).
Proof.
uhg. ir;eapply product_pr;am.
Qed.

Lemma superrel_relation : forall r, relation (superrel r).
Proof.
ir;ap product_relation.
Qed.

Lemma relates_superrel : forall r a b, relates r a b -> 
relates (superrel r) (union2 a b) (union2 a b).
Proof.
uf relates. uhg;ir.
ufi superrel H0. apply product_pr in H0. ee.
nin H0;clpri H1;clpri H2.
apply union2_or in H1;apply union2_or in H2.
rwi domain_inc_rw H1. rwi domain_inc_rw H2.
rwi range_inc_rw H1;rwi range_inc_rw H2.
rw product_pair_rw. rw union2_rw. rw union2_rw.
ee.
 nin H1;nin H0;apply H in H0;apply product_pair_pr in H0;ee;au.
 nin H2;nin H0;apply H in H0;apply product_pair_pr in H0;ee;au.
Qed.

Lemma product_related_rw : forall a b x y, R (product a b) x y = (inc x a & inc y b).
Proof.
ap product_pair_rw.
Qed.

Lemma superrel_rw : forall r x y, R (superrel r) x y =
 ((exists b : E, R r x b) \/ (exists a : E, R r a x) &
 (exists b : E, R r y b) \/ (exists a : E, R r a y)).
Proof.
ir. uf superrel.
 rw product_related_rw. rw union2_rw. rw union2_rw.
 repeat rw domain_inc_rw. repeat rw range_inc_rw.
tv.
Qed.

Lemma superrel_reverse : forall r, superrel (reverse r) = superrel r.
Proof.
ir; ap extensionality;intros a H.
assert (is_pair a). eapply product_pr;am.
nin H0.
change (R (superrel (reverse r)) a b) in H.
rwi superrel_rw H.
change (R (superrel (r)) a b).
rw superrel_rw.
repeat rwi reverse_R_rw H. ee;tauto.

assert (is_pair a). eapply product_pr;am.
nin H0.
change (R (superrel r) a b) in H.
rwi superrel_rw H.
change (R (superrel (reverse r)) a b).
rw superrel_rw.
repeat rw reverse_R_rw. ee;tauto.
Qed.

Lemma reverse_superrel : forall r, reverse (superrel r) = superrel r.
Proof.
ir; ap extensionality;intros a H.
assert (relation (superrel r)). eapply relates_relation. ap sub_refl.
wri reverse_relation H0.
cp (H0 a H). nin H1.
apply reverse_pair in H.
rwi superrel_rw H. 
change (R (superrel r) a b). rw superrel_rw. tauto.

assert (relation (superrel r)). eapply relates_relation. ap sub_refl.
cp (H0 a H);nin H1.
change (R (superrel r) a b) in H. rwi superrel_rw H.
ap pair_reverse. rw superrel_rw. tauto.
Qed.

Lemma relation_relates : forall r, relation r -> relates r (domain r) (range r).
Proof.
uhg;uhg;ir.
cp (H a H0). nin H1.
rw product_pair_rw. rw domain_inc_rw.
rw range_inc_rw.
ee;eauto.
Qed.

Lemma relation_relates_endo : forall r, relation r -> exists a, relates r a a.
Proof.
ir.
pose (a := union2 (domain r) (range r)).
cp union2_inc.
exists a;uhg;uhg;ir.
cp H1. apply H in H1.
nin H1.
ap product_pair_inc.
ap H0. left. ap domain_inc. exists b;am.
ap H0. right. ap range_inc. exists a0;am.
Qed.

Lemma relation_sub_relation : forall r, relation r -> forall r', sub r' r -> relation r'.
Proof.
uhg;ir. ap H;ap H0;am.
Qed.

Lemma sub_superrel : forall r, sub r (superrel r) -> relation r.
Proof.
intro. ap relation_sub_relation. ap superrel_relation.
Qed.

Lemma relates_sub_l : forall r a b, relates r a b -> sub (domain r) a.
Proof.
uhg;ir. apply domain_range_ex in H0. nin H0.
apply H in H0. apply product_pair_pr in H0;am.
Qed.

Lemma relates_sub_r : forall r a b, relates r a b -> sub (range r) b.
Proof.
uhg;ir. apply range_domain_ex in H0. nin H0.
apply H in H0. apply product_pair_pr in H0;am.
Qed.

Lemma reverse_domain : forall r, domain (reverse r) = range r.
Proof.
ir. ap extensionality_rw. ir.
rw domain_inc_rw. rw range_inc_rw.
rw reverse_R_rw. tv.
Qed.

Lemma reverse_range : forall r, range (reverse r) = domain r.
Proof.
ir. wr (reverse_reverse r).
rw reverse_domain.
rw reverse_reverse. tv.
Qed.

Definition symmetric_rel r := (forall x y, R r x y -> R r y x).

Definition transitive_rel r := forall x y, R r x y -> forall z, R r y z -> R r x z.

Definition reflexive_rel r a := (forall x, inc x a -> R r x x).

Definition antisymmetric_rel r := forall x y, R r x y -> R r y x -> x=y.

Definition irreflexive_rel r := forall x, ~ R r x x.


Lemma superrel_trans : forall r, transitive_rel (superrel r).
Proof.
uhg;ir.
rwi superrel_rw H. rwi superrel_rw H0.
ee.
rw superrel_rw. ee.
am. am.
Qed.

Lemma symm_rev_eq : forall r, symmetric_rel r -> reverse r = r.
Proof.
ir.
ap extensionality;uhg;ir.
Im_nin H0. destruct (P_dec (is_pair x)).
subst. ap H. nin i. clpr. am.
subst. am.

apply by_cases with (is_pair a);ir. nin H1.
ap pair_reverse. ap H. am.
ap Im_show_inc;exists a. ee. am.
rw P_dec_if_not;au.
Qed.

Lemma rev_eq_symm : forall r, reverse r = r -> symmetric_rel r.
Proof.
uhg;ir.
wr (reverse_reverse r). ap pair_reverse. rw H. am.
Qed.

Lemma symm_rev_rw : forall r, symmetric_rel r = (reverse r = r).
Proof.
ir;ap iff_eq.
 ap symm_rev_eq.
 ap rev_eq_symm.
Qed.

Lemma superrel_symm : forall r, symmetric_rel (superrel r).
Proof.
ir. ap rev_eq_symm. ap reverse_superrel.
Qed.

Lemma superrel_refl : forall r a, sub a (union2 (domain r) (range r)) -> 
reflexive_rel (superrel r) a.
Proof.
uhg;ir.
ap product_pair_inc;ap H;am.
Qed.

Section Relator_rewrites.

Variables (r a : E).
Hypothesis (Hrel : relates r a a).

Lemma symm_symmT : symmetric_rel r -> symmetricT (R r) a.
Proof.
ir. uhg;ir.
ap H;am.
Qed.

Lemma symmT_symm : symmetricT (R r) a -> symmetric_rel r.
Proof.
uhg. ir.
ap H.
eapply relates_inc_l;am. eapply relates_inc_r;am.
am.
Qed.

Lemma symm_rel_rw : symmetricT (R r) a = symmetric_rel r.
Proof.
ap iff_eq. ap symmT_symm.
ap symm_symmT.
Qed.

Lemma trans_transT : transitive_rel r -> transitiveT (R r) a.
Proof.
uhg;ir. eapply H;am.
Qed.

Lemma transT_trans : transitiveT (R r) a -> transitive_rel r.
Proof.
uhg;ir.
cp (relates_inc Hrel H0). ee.
cp (relates_inc_r Hrel H1).
apply H with y;am.
Qed.

Lemma transT_trans_rw : transitiveT (R r) a = transitive_rel r.
Proof.
ap iff_eq.
ap transT_trans.
ap trans_transT.
Qed.

Lemma refl_reflT : reflexive_rel r a -> reflexiveT (R r) a.
Proof.
uhg. uf reflexive_rel. intro. ee.
am.
Qed.

Lemma reflT_refl : reflexiveT (R r) a -> reflexive_rel r a.
Proof.
uhg;ir.
ap H. am.
Qed.

Lemma reflT_refl_rw : reflexiveT (R r) a = reflexive_rel r a.
Proof.
tv. 
Qed.

Lemma antisym_antisymT : antisymmetric_rel r -> antisymmetricT (R r) a.
Proof.
uhg;ir. ap H. am. am.
Qed.

Lemma antisymT_antisym : antisymmetricT (R r) a -> antisymmetric_rel r.
Proof.
uhg;ir. ap H.
eapply relates_inc_l;am.
eapply relates_inc_l;am.
am. am.
Qed.

Lemma antisymT_antisym_rw : antisymmetricT (R r) a = antisymmetric_rel r.
Proof.
ap iff_eq.
ap antisymT_antisym.
ap antisym_antisymT.
Qed.

Lemma irrefl_irreflT : irreflexive_rel r -> irreflexiveT (R r) a.
Proof.
uhg;ir. ap H.
Qed.

Lemma irreflT_irrefl : irreflexiveT (R r) a -> irreflexive_rel r.
Proof.
uhg;ir. uhg;ir. apply H with x.
eapply relates_inc_l;am. am.
Qed.

Lemma irreflT_refl_rw : irreflexiveT (R r) a = irreflexive_rel r.
Proof.
ap iff_eq.
ap irreflT_irrefl.
ap irrefl_irreflT.
Qed.

End Relator_rewrites.

Section Closure.

Definition trans_clos r := inter (Z (powerset (superrel r))
   (fun r' => sub r r' & transitive_rel r')).

Lemma trans_clos_superrel_aux : forall r a, relates r a a ->
 sub (trans_clos r) (superrel r).
Proof.
uhg;intros r a Hr;ir.
assert (inc (superrel r) (powerset (superrel r))).
ap powerset_inc. ap sub_refl.
assert (inc (superrel r) (Z (powerset (superrel r))
   (fun r' : E => r ⊂ r' & transitive_rel r'))).
ap Z_inc. am.
ee. ap superrel_sub.
eapply relates_relation. am.
ap superrel_trans.
eapply inter_all;am.
Qed.

Lemma trans_clos_nonrel : forall r, ~ relation r -> trans_clos r = emptyset.
Proof.
ir. ap empty_emptyset;ir.
apply Z_sub in H0.
apply union_ex in H0. nin H0.
ee. apply Z_all in H0. ee.
apply powerset_sub in H0.
ap H.
apply relation_sub_relation with (superrel r). 
ap product_relation.
eapply sub_trans;am.
Qed.

Lemma trans_clos_superrel : forall r, sub (trans_clos r) (superrel r).
Proof.
ir. apply by_cases with (relation r);ir.
apply relation_relates_endo in H. nin H.
apply trans_clos_superrel_aux with x;am.

replace (trans_clos r) with emptyset. ap emptyset_sub_all.
symmetry. ap trans_clos_nonrel. am.
Qed.

Lemma trans_clos_nonempty_aux : forall r, relation r -> nonempty
  (Z (powerset (superrel r)) (fun r' : E => r ⊂ r' & transitive_rel r')).
Proof.
ir.
exists (superrel r). ap Z_inc. ap powerset_inc;ap sub_refl.
ee. ap superrel_sub. am.
ap superrel_trans.
Qed.

Lemma trans_clos_sub : forall r, relation r -> sub r (trans_clos r).
Proof.
ir. uhg;ir.
ap inter_inc.
ap trans_clos_nonempty_aux. am.
ir. apply Z_pr in H1. ee.
au.
Qed.

Lemma trans_clos_smallest : forall r, relation r -> forall r',
sub r r' -> transitive_rel r' -> sub (trans_clos r) r'.
Proof.
ir.
uhg;ir.
assert (forall k, inc k (Z (powerset (superrel r))
            (fun r' : E => r ⊂ r' & transitive_rel r')) -> inc a k).
ap inter_all. am.
assert (forall k, sub k (superrel r) -> sub r k -> transitive_rel k -> inc a k).
ir;ap H3. ap Z_inc. ap powerset_inc;am. ee;am.
clear H3.
assert (forall k, sub r k -> transitive_rel k -> inc a k).
ir. assert (inc a (inter2 k (superrel r))).
ap H4. ap inter2_r. 
uhg;ir. ap inter2_inc. au. ap superrel_sub.
(* here use relation r*)
am.
am.
uhg;ir. apply inter2_and in H6;apply inter2_and in H7. ee.
ap inter2_inc. apply H5 with y;am. apply superrel_trans with y;am.
eapply inter2_l;am. clear H4.
ap H3. am. am.
Qed.

Lemma trans_clos_trans : forall r, transitive_rel (trans_clos r).
Proof.
ir. apply by_cases with (relation r);ir.

Focus 2. rw trans_clos_nonrel. uhg;ir. ufi R H0. emptyset_auto.
am.

uhg;ir.
ufa R.
ap inter_inc. ap trans_clos_nonempty_aux. am.
ir. apply Z_all in H2;ee.
apply H4 with y.
eapply inter_all. am.
ap Z_inc. am. ee. am. am.
eapply inter_all. am.
ap Z_inc;ee;am.
Qed.

Section Reachable.

Variable (R : E2P).

Inductive reachable : E2P :=
  | R_reach : forall x y, R x y -> reachable x y
  | reach_trans : forall x y, reachable x y -> forall z, reachable y z -> reachable x z
.

Lemma reachable_trans : forall a, transitiveT reachable a.
Proof.
uhg. ir;apply reach_trans with y;am.
Qed.

Lemma reach_cons : forall x y, R x y -> forall z, reachable y z -> reachable x z.
Proof.
intros ? ? ?.
ap reach_trans. constructor. am.
Qed.

Inductive path_n : nat -> E -> E -> Type :=
  | path_0 : forall x, path_n 0 x x
  | path_S : forall x y, R x y -> forall n z, path_n n y z -> path_n (S n) x z
.

Lemma path_0_eq : forall x y, path_n 0 x y -> x=y.
Proof.
ir. inversion X;au.
Qed.

Lemma path_n_reach : forall n x y, path_n (S n) x y -> reachable x y.
Proof.
assert (forall n, n<>0 -> forall x y, path_n n x y -> reachable x y).
ir. nin X. nin H;tv.
destruct n.
apply path_0_eq in X. subst. constructor;am.
apply reach_cons with y. am. ap IHX. uhg;ir.
inversion H0.

ir;eapply H;try am. uhg;ir;inversion H0.
Qed.

Definition path_n_trans : forall n x y, path_n n x y -> forall m z, path_n m y z -> 
path_n (n+m) x z.
intros ? ? ? H.
nin H.
ir. simpl. am.
ir. simpl.
eapply path_S. am. ap IHpath_n. am.
Defined.

Lemma reach_path_n : forall x y, reachable x y ->
 exists n, n<>0 & nonemptyT (path_n n x y).
Proof.
ir. nin H.
exists 1. ee. uhg;ir;inversion H0. econstructor.
eapply path_S. am. constructor.
nin IHreachable1;nin IHreachable2. ee.
nin H3;nin H4.
exists (x0+x1).
ee. uhg;ir;destruct x0. nin H1;tv. inversion H3.
 econstructor.
eapply path_n_trans. am. am.
Qed.

Lemma reach_smallest : forall R' : E2P, (forall x y, R x y -> R' x y) -> 
(forall x y, R' x y -> forall z, R' y z -> R' x z) -> 
forall x y, reachable x y -> R' x y.
Proof.
ir.
nin H1. ap H;am.
apply H0 with y;am.
Qed.

Lemma trans_reach_eq : (forall x y, R x y -> forall z, R y z -> R x z) -> 
reachable = R.
Proof.
ir;ap arrow_extensionality;intros x;ap arrow_extensionality;intros y.
ap iff_eq;ir.
nin H0. am. apply H with y;am.
ap R_reach. am.
Qed.

Lemma reachable_domain : forall x y, reachable x y -> exists y', R x y'.
Proof.
ir. nin H.
exists y;am.
am.
Qed.

Lemma reachable_range : forall x y, reachable x y -> exists x', R x' y.
Proof.
ir;nin H.
exists x;am.
am.
Qed.

End Reachable.

Lemma reach_trans_clos : forall r, relation r -> forall x y, reachable (R r) x y -> 
R (trans_clos r) x y.
Proof.
ir. nin H0.
ap trans_clos_sub. am. am.
apply trans_clos_trans with y;am.
Qed.

Lemma relation_ex : forall r, exists r', relation r' & R r = R r'.
Proof.
ir. exists (Z r is_pair). ee.
uhg. ap Z_pr.
ap arrow_extensionality;ir;ap arrow_extensionality;ir.
ap iff_eq;ir.
ap Z_inc. am. ap pair_is_pair.
eapply Z_sub;am.
Qed.

Lemma same_rel_eq : forall r, relation r -> forall r', relation r' -> 
R r = R r' -> r=r'.
Proof.
ir;ap extensionality_rw;ir.
apply by_cases with (is_pair a);ir. nin H2.
change (R r a b = R r' a b). rw H1;tv.
ap iff_eq;ir;nin H2;au.
Qed.

Lemma reachable_rel : forall r, exists r', relation r' & reachable (R r) = R r'.
Proof.
ir.
exists (Z (product (domain r) (range r)) (fun p => reachable (R r) (P p) (Q p))).
ee. uhg;ir. apply Z_sub in H;eapply product_pr;am.
ap arrow_extensionality;ir;ap arrow_extensionality;intro b.
ap iff_eq;ir.
cp (reachable_domain H).
cp (reachable_range H).
ap Z_inc. ap product_pair_inc.
ap domain_inc. am.
ap range_inc;am.
clpr. am.

apply Z_pr in H. clpri H. am.
Qed.

Lemma relation_sub : forall r, relation r -> forall r',
 (forall x y, R r x y -> R r' x y) = sub r r'.
Proof.
ir;ap iff_eq;ir.
uhg;ir. cp (H a H1). nin H2. ap H0;am.
ap H0;am.
Qed.

Lemma trans_clos_reach : forall r, relation r ->
 forall x y, R (trans_clos r) x y -> reachable (R r) x y.
Proof.
intros ? Hr;ir.
cp (reachable_rel r).
destruct H0 as [r' H0];ee.
rw H1.
eapply trans_clos_smallest. Focus 4.
am.
am.
wr relation_sub. wr H1. 
ap R_reach.
am.
uhg. wr H1. ap reach_trans.
Qed.

Lemma trans_clos_reach_rw : forall r, relation r ->
 R (trans_clos r) = reachable (R r).
Proof.
ir.
ap arrow_extensionality;ir;ap arrow_extensionality;ir.
ap iff_eq. ap trans_clos_reach. am.
ap reach_trans_clos. am.
Qed.



End Closure.

End Relation.
Export Relation.

Module Function.

Definition axioms f := and (relation f) (functional f).

Definition ev f x := union (range (Z f (fun p => eq x (P p)))).

(*
Definition ev f x := choose (fun y => inc (pair x y) f).
*)


Lemma fun_show_ev : forall f, axioms f -> forall x y, inc (pair x y) f -> 
y = ev f x.
Proof.
ir.
uf ev.
ap extensionality;uhg;ir.
ap union_inc. econstructor. ee.
ap range_inc.
exists x. ap Z_inc. am. clpr;tv. am.

apply union_ex in H1;nin H1;ee.
apply range_domain_ex in H1. nin H1.
apply Z_all in H1. ee.
clpri H3. subst.
uh H. ee. uh H3. cp (H3 x1 x0 H1 y H0). subst. am.
Qed.

Lemma domain_ev_inc : forall f x, axioms f -> inc x (domain f) -> 
inc (pair x (ev f x)) f.
Proof.
ir. ufi domain H0.
apply Z_all in H0;ee. nin H1;ee.
assert (x0 = ev f x). ap fun_show_ev. am.
am. subst. am.
Qed.

Lemma domain_P_in : forall f, axioms f -> forall x, inc x f -> 
inc (P x) (domain f).
Proof.
intros f Hf. ap domain_rel_P_in.
am.
Qed.

Lemma domain_P_rw : forall f, axioms f -> domain f = Im P f.
Proof.
ir. ap extensionality;uhg;ir.
apply Z_pr in H0. nin H0.
ap Im_show_inc. exists (pair a x). ee. am.
clpr. tv.
apply Im_ex in H0;nin H0. ee;subst.
ap domain_P_in. am. am.
Qed.


Lemma range_ev_inc : forall f, axioms f -> forall x, inc x (domain f) ->
 inc (ev f x) (range f).
Proof.
ir. ap range_inc. exists x. ap domain_ev_inc.
am. am.
Qed.

Lemma range_show_inc : forall f, axioms f -> forall y,
 (exists x, inc x (domain f) & ev f x = y) -> 
inc y (range f).
Proof.
ir. nin H0;ee;subst. ap range_ev_inc. am. am.
Qed.

Lemma fun_ev_eq : forall f, axioms f -> forall x, inc x f -> 
x = pair (P x) (ev f (P x)).
Proof.
ir. cp H0.
apply H in H0. nin H0. clpr.
uh H;ee. assert (b = (ev f a)).
ap fun_show_ev. uhg;ee;am.
am.
subst. tv.
Qed.

Lemma fun_Q_ev : forall f, axioms f -> forall x, inc x f -> 
Q x = ev f (P x).
Proof.
ir. apply fun_ev_eq in H0. rw H0. clpr. tv. am.
Qed.

Lemma range_ex : forall f, axioms f -> forall y, inc y (range f) -> 
exists x, inc x (domain f) & y = ev f x.
Proof.
ir.
apply range_domain_ex in H0. nin H0.
exists x;ee. ap domain_inc. exists y;am.
ap fun_show_ev. am. am.
Qed.

Lemma range_Q_rw : forall f, axioms f -> range f = Im Q f.
Proof.
ir. uf range. ap uneq.
ap extensionality. ap Z_sub.
uhg;ir;ap Z_inc. am. ap H;am.
Qed.

Lemma range_Im_rw : forall f, axioms f -> range f = Im (ev f) (domain f).
Proof.
ir.
ap extensionality;uhg;ir.
apply range_ex in H0. nin H0;ee. subst.
ap Im_inc. am.
am.
apply Im_ex in H0. nin H0;ee;subst.
ap range_ev_inc. am.
am.
Qed.

Lemma sub_axioms : forall f, axioms f -> forall g, sub g f -> axioms g.
Proof.
ir.
uhg;uh H;ee;intro;ir. 
ap H. au.
intro;ir. eapply H1. ap H0;am. ap H0;am.
Qed.

Lemma function_sub : forall f g, axioms f -> axioms g -> 
sub (domain g) (domain f) -> 
(forall x, inc x (domain g) -> ev f x = ev g x) -> 
sub g f.
Proof.
ir.
uhg;ir.
cp H3. apply H0 in H4.
nin H4.
assert (inc a (domain g)).
ap domain_inc. exists b;am.
cp H3. apply fun_Q_ev in H5. clpri H5.
subst.
wr H2.
ap domain_ev_inc. am. ap H1. am.
am. am.
Qed.

Lemma function_extensionality : forall f g, axioms f -> axioms g -> 
(domain f = domain g) -> 
(forall x, inc x (domain f) -> ev f x = ev g x) -> 
f=g.
Proof.
ir. ap extensionality;ap function_sub;try am.
rw H1. ap sub_refl.
ir. symmetry. ap H2. am.
rw H1;ap sub_refl.
ir. ap H2. rw H1. am.
Qed.

Lemma singleton_axioms : forall a b, axioms (singleton (J a b)).
Proof.
ir;uhg;ee;uhg;ir.
apply singleton_eq in H. subst;ap pair_is_pair.
uhg;ir;apply singleton_eq in H;apply singleton_eq in H0.
apply pair_eq in H;apply pair_eq in H0;ee. rw H1;am.
Qed.

Lemma singleton_domain : forall a b, domain (singleton (J a b)) = singleton a.
Proof.
ir;ap extensionality;uhg;ir.
apply domain_ev_inc in H. apply singleton_eq in H. apply pair_eq in H;ee.
rw H;ap singleton_inc.
ap singleton_axioms.
apply singleton_eq in H;subst.
ap domain_inc. exists b;ap singleton_inc.
Qed.

Definition create a f := Im (fun x => pair x (f x)) a.

Lemma create_emptyset : forall f, create emptyset f = emptyset.
Proof.
ir;ap empty_emptyset;ir.
ufi create H. apply Im_ex in H;nin H.
ee. apply emptyset_empty with x;am.
Qed.

Lemma create_axioms : forall a f, axioms (create a f).
Proof.
ir. uhg;ee;uhg;ir.
apply Im_ex in H. nin H. ee. subst. ap pair_is_pair.
uhg;ir;apply Im_ex in H;apply Im_ex in H0;nin H;nin H0;ee;subst.
apply pair_eq in H2. ee;subst. apply pair_eq in H1;ee;subst. tv.
Qed.

Lemma create_domain : forall a f, domain (create a f) = a.
Proof.
ir.
ap extensionality;uhg;ir.
rwi domain_P_rw H. apply Im_ex in H. nin H;ee;subst.
apply Im_ex in H;nin H;ee;subst. clpr. am.
ap create_axioms.
rw domain_P_rw. ap Im_show_inc. econstructor.
ee. ap Im_show_inc. econstructor. ee.
am. reflexivity. clpr. tv.
ap create_axioms.
Qed.

Lemma emptyset_axioms : axioms emptyset.
Proof.
wr (create_emptyset (fun x => x)). ap create_axioms.
Qed.

Lemma emptyset_domain : domain emptyset = emptyset.
Proof.
uf domain;ap empty_emptyset;ir.
apply Z_pr in H;nin H;ee. apply emptyset_empty in H;am.
Qed.

Lemma create_ev : forall a f, forall x, inc x a -> 
ev (create a f) x = f x.
Proof.
ir.
symmetry. ap fun_show_ev.
ap create_axioms.
ap Im_show_inc. exists x;ee.
am. tv.
Qed.

Lemma create_in : forall a f x y, inc (pair x y) (create a f) -> 
y = f x.
Proof.
ir.
apply Im_ex in H;nin H;ee;subst. apply pair_eq in H0;ee;subst. tv.
Qed.

Lemma domain_sub : forall f g, sub f g -> sub (domain f) (domain g).
Proof.
ir;uhg;ir.
ap domain_inc. apply Z_pr in H0. nin H0. exists x. au.
Qed.

Lemma range_sub : forall f g, sub f g -> sub (range f) (range g).
Proof.
ir;uhg;ir. ap range_inc.
apply range_domain_ex in H0. nin H0;exists x;au.
Qed.

Lemma create_range : forall a f, range (create a f) = Im f a.
Proof.
ir.
ap extensionality;uhg;ir.
apply range_ex in H.
nin H;ee;subst. rwi create_domain H.
rw create_ev. ap Im_inc. am. am. ap create_axioms.
apply Im_ex in H;nin H;ee;subst.
ap range_inc. exists x. ap Im_show_inc. exists x;ee;au.
Qed.

Lemma Im_ev_create : forall x f, Im (ev (create x f)) x = Im f x.
Proof.
ir;ap extensionality;uhg;ir.
apply Im_ex in H;nin H;ee. subst. rw create_ev;au.
ap Im_inc;am.
apply Im_ex in H;nin H;ee;subst.
ap Im_show_inc. exists x0;ee;au.
rw create_ev;au.
Qed.

Lemma trans_of_ev : forall f, axioms f ->
 Application.axioms (domain f) (range f) (ev f).
Proof.
ir;uhg;ir.
ap range_ev_inc. am. am.
Qed.

Lemma create_recov : forall f, axioms f -> f = create (domain f) (ev f).
Proof.
ir. ap function_extensionality. am.
ap create_axioms.
symmetry. ap create_domain.
ir.
symmetry.
ap create_ev.
am.
Qed.

Definition inverse_image a f := Z (domain f) (fun x => inc (ev f x) a).

Lemma create_extensionality : forall a f g, (forall x, inc x a -> f x = g x) -> 
create a f = create a g.
Proof.
ir.
ap function_extensionality;try ap create_axioms.
rw create_domain. rw create_domain. tv.
ir. rwi create_domain H0.
rw create_ev. rw create_ev. ap H;am. am. am.
Qed.

Lemma create_replace_inner : forall a b f g h, (forall x, inc x a -> inc (h x) b) ->
 create a (fun x => g (ev (create b f) (h x))) = create a (fun x => g (f (h x))).
Proof.
ir. ap create_extensionality.
ir. ap uneq. ap create_ev. ap H. am.
Qed.

Lemma create_create_sub : forall a b, sub a b -> forall f, 
create a (ev (create b f)) = create a f.
Proof.
ir. transitivity (create a (fun x => ev (create b f) x)).
ap uneq. ap arrow_extensionality. ir;tv.
cp create_replace_inner.
cp (H0 a b f (fun v => v) (fun v => v)).
clear H0. simpl in H1. rw H1.
ap uneq. ap arrow_extensionality;ir;tv.
am.
Qed.

Lemma create_create : forall a f, create a (ev (create a f)) = create a f.
Proof.
ir. ap create_create_sub.
ap sub_refl.
Qed.

Definition composable f g := 
and (axioms f)
(and (axioms g)
(sub (range g) (domain f))).

Definition compose f g := create (inverse_image (domain f) g)
 (fun x => ev f (ev g x)).

Lemma compose_axioms : forall f g, axioms (compose f g).
Proof.
ir;ap create_axioms.
Qed.

Lemma compose_domain : forall f g, domain (compose f g) =
 inverse_image (domain f) g.
Proof.
ir. ap create_domain.
Qed.

Lemma composable_domain : forall f g, composable f g -> 
domain (compose f g) = domain g.
Proof.
ir.
rw compose_domain.
ap extensionality;uhg;ir.
apply Z_all in H0. ee. am.

ap Z_inc. am.
uh H;ee.
ap H2. ap range_ev_inc. am.
am.
Qed.

Lemma compose_ev : forall f g x, inc x (domain (compose f g)) -> 
ev (compose f g) x = ev f (ev g x).
Proof.
ir. uf compose. rwi compose_domain H.
rw create_ev.
tv. am.
Qed.

Definition id x := create x (fun y => y).

Lemma id_axioms : forall x, axioms (id x).
Proof.
ir;ap create_axioms.
Qed.

Lemma id_domain : forall x, domain (id x) = x.
Proof.
ir;ap create_domain.
Qed.

Lemma id_range : forall x, range (id x) = x.
Proof.
ir. uf id. rw create_range.
ap extensionality;uhg;ir.

apply Im_ex in H;nin H;ee;subst;am.
ap Im_show_inc. exists a;ee. am. tv.
Qed.

Lemma id_ev : forall x y, inc y x -> ev (id x) y = y.
Proof.
ir. uf id. ap create_ev. am.
Qed.

Lemma id_composable_l : forall f, axioms f -> forall x, sub (range f) x -> 
composable (id x) f.
Proof.
ir;uhg;ee. ap id_axioms. am.
rw id_domain. am.
Qed.

Lemma id_composable_r : forall f, axioms f -> forall x, sub x (domain f) -> 
composable f (id x).
Proof.
ir.
uhg;ee. am. ap id_axioms.
rw id_range. am.
Qed.

Lemma compose_id_l : forall f, axioms f -> compose (id (range f)) f = f.
Proof.
ir. ap function_extensionality.
ap compose_axioms. am.
rw composable_domain.
tv. ap id_composable_l. am. ap sub_refl.
ir.
rwi composable_domain H0.
rw compose_ev. rw id_ev. tv.
ap range_ev_inc. am. am.
rw composable_domain. am.
ap id_composable_l. am. ap sub_refl.
ap id_composable_l. am. ap sub_refl.
Qed.

Lemma compose_id_r : forall f, axioms f -> compose f (id (domain f)) = f.
Proof.
ir.
ap function_extensionality.
ap compose_axioms. am.
rw composable_domain.
ap id_domain. ap id_composable_r. am. ap sub_refl.
ir.
rwi composable_domain H0. rwi id_domain H0.
rw compose_ev. rw id_ev. tv.
am. rw composable_domain. rw id_domain. am.
ap id_composable_r. am. ap sub_refl.
ap id_composable_r. am. ap sub_refl.
Qed.

Lemma compose_assoc : forall f g h, axioms f -> axioms g -> axioms h -> 
compose f (compose g h) = compose (compose f g) h.
Proof.
ir. cp compose_axioms.
assert (domain (compose f (compose g h)) = domain (compose (compose f g) h)).
repeat rw compose_domain.
ap extensionality;uhg;ir.
apply Z_all in H3. ee.
rwi compose_ev H4;au.
rwi compose_domain H3. apply Z_all in H3;ee.
ap Z_inc. am. ap Z_inc. am. am.
apply Z_all in H3;ee.
apply Z_all in H4;ee.
ap Z_inc. rw compose_domain. ap Z_inc;au. rw compose_ev.
am. rw compose_domain. ap Z_inc;au.

ap function_extensionality;au.

ir. rw compose_ev;au.
rwi H3 H4. symmetry; rw compose_ev;au;symmetry.
rwi compose_domain H4. apply Z_all in H4.
ee. rwi compose_domain H5;apply Z_all in H5;ee.
rw compose_ev. rw compose_ev. tv.
rw compose_domain. ap Z_inc;au.
rw compose_domain;ap Z_inc;au.
Qed.


Definition restr f x := Z f (fun a => inc (P a) x).

Lemma restr_axioms : forall f x, axioms f -> axioms (restr f x).
Proof.
ir. apply sub_axioms with f. am. ap Z_sub.
Qed.

Lemma restr_domain : forall f x, axioms f ->
 domain (restr f x) = inter2 (domain f) x.
Proof.
ir.
rw domain_P_rw. rw domain_P_rw.
ap extensionality;uhg;ir.
apply Im_ex in H0;nin H0;ee;subst.
apply Z_all in H0;ee.
ap inter2_inc. ap Im_inc. am.
am.
apply inter2_and in H0. ee.
apply Im_ex in H0;nin H0;ee;subst.
ap Im_inc. ap Z_inc. am. am.
am. ap restr_axioms. am.
Qed.

Lemma restr_sub_domain : forall f x, axioms f -> sub x (domain f) ->
 domain (restr f x) = x.
Proof.
ir. rw restr_domain;au. ap extensionality;uhg;ir.
eapply inter2_r;am. ap inter2_inc;au.
Qed.

Lemma restr_ev : forall f, axioms f -> forall a x, inc x a -> inc x (domain f) ->
 ev (restr f a) x = ev f x.
Proof.
ir. symmetry.
ap fun_show_ev. ap restr_axioms. am.

ap Z_inc. ap domain_ev_inc. am. am.
clpr. am.
Qed.

Lemma restr_sub_ev : forall f, axioms f -> forall a, sub a (domain f) -> 
forall x, inc x a -> ev (restr f a) x = ev f x.
Proof.
ir. ap restr_ev. am. am. au.
Qed.

Lemma restr_recov : forall f, axioms f -> restr f (domain f) = f.
Proof.
ir.
ap function_extensionality.
ap restr_axioms. am. am.
rw restr_domain. ap extensionality;uhg;ir.
apply inter2_and in H0. am.
ap inter2_inc;am.
am.

ir.
rwi restr_domain H0. apply inter2_and in H0;ee. clear H1.
rw restr_sub_ev.
tv.
am. ap sub_refl.
am. am.
Qed.

Lemma sub_ev_eq : forall f g, axioms f -> sub g f -> forall x, inc x (domain g) -> 
ev g x = ev f x.
Proof.
ir.
ap fun_show_ev. am.
ap H0. ap domain_ev_inc. apply sub_axioms with f. am. am. am.
Qed.

Lemma restr_eq : forall f, axioms f -> forall g, axioms g -> 
sub (domain f) (domain g) -> (forall x , inc x (domain f) -> ev f x = ev g x) -> 
restr g (domain f) = f.
Proof.
ir.
ap function_extensionality;ir.
ap restr_axioms;am.
am.
ap restr_sub_domain. am. am.

rw restr_ev. rwi restr_sub_domain H3;au.
symmetry;ap H2;am. rwi restr_sub_domain H3;au. 
rwi restr_sub_domain H3;au. 
rwi restr_sub_domain H3;au. 
Qed.

Notation L := create.

Definition union_strict_cond e := forall f, inc f e -> forall g, inc g e -> 
forall x, inc x (domain f) -> inc x (domain g) -> f = g.

Lemma union_strict_cond_rw : union_strict_cond = fun e => 
(forall f g, inc f e -> inc g e -> nonempty (inter2 (domain f) (domain g)) -> f=g).
Proof.
ap arrow_extensionality. intros e.
ap iff_eq;try uhg;ir.
nin H2. apply inter2_and in H2. ee.
eapply H;try am.
ap H. am. am. exists x. ap inter2_inc. am. am.
Qed.

Lemma union_axioms : forall e, (forall f, inc f e -> axioms f) -> 
union_strict_cond e -> 
axioms (union e).
Proof.
rw union_strict_cond_rw.
ir;uhg;ee;uhg;ir.
apply union_ex in H1;nin H1;ee.
eapply H. am. am.
uhg;ir;apply union_ex in H1;apply union_ex in H2.
nin H1;nin H2;ee.

assert (x0=x1). ap H0.
am. am. exists x. ap inter2_inc;
ap domain_inc.
exists y. am. exists y'. am.
subst.
eapply H. am. am. am.
Qed.

Lemma union2_axioms : forall f g, axioms f -> axioms g ->
 inter2 (domain f) (domain g) = emptyset -> 
axioms (union2 f g).
Proof.
ir;uf union2;ap union_axioms.
ir. apply doubleton_or in H2. nin H2;subst;am.
uhg;ir.
apply doubleton_or in H2;apply doubleton_or in H3.
cp (inter2_inc H4 H5).
nin H2;nin H3;subst.
tv. rwi H1 H6. apply emptyset_empty in H6. nin H6.
rwi inter2_comm H6. rwi H1 H6. apply emptyset_empty in H6. nin H6.
tv.
Qed.

Lemma union_domain : forall e, (forall f, inc f e -> axioms f) -> 
union_strict_cond e -> 
domain (union e) = union (Im domain e).
Proof.
rw union_strict_cond_rw.
ir.
ap extensionality;uhg;ir.
apply domain_ev_inc in H1. apply union_ex in H1.
nin H1;ee.
ap union_inc. econstructor;ee.
ap Im_inc. am. ap domain_inc. econstructor;am.
ap union_axioms;try am. rw union_strict_cond_rw;am.
apply union_ex in H1;nin H1;ee.
apply Im_ex in H1. nin H1;ee;subst.
ap domain_inc.
apply domain_ev_inc in H2.
econstructor. ap union_inc. econstructor;ee. am. am.
ap H;am.
Qed.

Lemma union2_domain : forall f g, axioms f -> axioms g ->
 inter2 (domain f) (domain g) = emptyset -> 
domain (union2 f g) = union2 (domain f) (domain g).
Proof.
ir;uf union2. rw union_domain;try rw union_strict_cond.
ap uneq. ap extensionality_rw. ir. rw Im_rw. ap iff_eq;ir.
nin H2;ee. subst. apply doubleton_or in H2;nin H2;subst.
ap doubleton_l. ap doubleton_r.
apply doubleton_or in H2;nin H2;subst;econstructor;ee;try reflexivity.
ap doubleton_l. ap doubleton_r.

ir. apply doubleton_or in H2. nin H2;subst;am.
rw union_strict_cond_rw. ir. nin H4.
apply doubleton_or in H2;apply doubleton_or in H3.
nin H2;nin H3;subst.
tv. rwi H1 H4. apply emptyset_empty in H4. nin H4.
rwi inter2_comm H4. rwi H1 H4. apply emptyset_empty in H4. nin H4.
tv.
Qed.

Lemma union_ev : forall e, (forall f, inc f e -> axioms f) -> 
union_strict_cond e ->
forall f, inc f e -> forall x, inc x (domain f) -> ev (union e) x = ev f x.
Proof.
ir.
assert (inc x (domain (union e))).
rw union_domain;try am. ap union_inc;econstructor.
ee. ap Im_inc. am. am.
apply domain_ev_inc in H3. 
assert (axioms (union e)). ap union_axioms. am. am.
apply H4 with x. am.
ap union_inc;econstructor. ee. am. ap domain_ev_inc. ap H;am. am.
ap union_axioms;am.
Qed.

Lemma union2_ev_l : forall f g, axioms f -> axioms g ->
 inter2 (domain f) (domain g) = emptyset -> 
forall x (Hinc : inc x (domain f)), ev (union2 f g) x = ev f x.
Proof.
ir. uf union2. ap union_ev.

ir. apply doubleton_or in H2. nin H2;subst;am.
rw union_strict_cond_rw;ir. nin H4.
apply doubleton_or in H2;apply doubleton_or in H3.
nin H2;nin H3;subst.
tv. rwi H1 H4. apply emptyset_empty in H4. nin H4.
rwi inter2_comm H4. rwi H1 H4. apply emptyset_empty in H4. nin H4.
tv.
ap doubleton_l.
am.
Qed.

Lemma union2_ev_r : forall f g, axioms f -> axioms g ->
 inter2 (domain f) (domain g) = emptyset -> 
forall x (Hinc : inc x (domain g)), ev (union2 f g) x = ev g x.
Proof.
ir. uf union2. ap union_ev.

ir. apply doubleton_or in H2. nin H2;subst;am.
rw union_strict_cond_rw. ir. nin H4.
apply doubleton_or in H2;apply doubleton_or in H3.
nin H2;nin H3;subst.
tv. rwi H1 H4. apply emptyset_empty in H4. nin H4.
rwi inter2_comm H4. rwi H1 H4. apply emptyset_empty in H4. nin H4.
tv.
ap doubleton_r.
am.
Qed.

Lemma union_range : forall e, (forall f, inc f e -> axioms f) -> 
union_strict_cond e ->
range (union e) = union (Im range e).
Proof.
ir. ap extensionality;uhg;ir.
apply range_ex in H1. nin H1;ee;subst.
rwi union_domain H1;try am.
apply union_ex in H1. nin H1;ee.
apply Im_ex in H1. nin H1;ee;subst.
ap union_inc;econstructor. ee.
ap Im_inc. am. ap range_show_inc.
ap H;am. econstructor;ee.
am. 
symmetry. ap union_ev. am. am.
am. am.
ap union_axioms;am.

ap range_show_inc.
ap union_axioms;am.
apply union_ex in H1;nin H1;ee.
apply Im_ex in H1;nin H1;ee;subst.
apply range_ex in H2. nin H2;ee;subst.
econstructor. ee. rw union_domain. ap union_inc;econstructor.
ee. ap Im_inc. am. am.
am. am.
ap union_ev. am. am. am. am.
ap H;am.
Qed.

Lemma union2_range :  forall f g, axioms f -> axioms g ->
 inter2 (domain f) (domain g) = emptyset -> 
range (union2 f g) = union2 (range f) (range g).
Proof.
ir. uf union2. etransitivity.
ap union_range.

ir. apply doubleton_or in H2. nin H2;subst;am.
rw union_strict_cond_rw. ir. nin H4.
apply doubleton_or in H2;apply doubleton_or in H3.
nin H2;nin H3;subst.
tv. rwi H1 H4. apply emptyset_empty in H4. nin H4.
rwi inter2_comm H4. rwi H1 H4. apply emptyset_empty in H4. nin H4.
tv.

ap uneq.
ap extensionality_rw;ir.
rw Im_rw. ap iff_eq;ir.
nin H2;ee;subst. apply doubleton_or in H2. nin H2;subst;[apply doubleton_l|apply doubleton_r].
apply doubleton_or in H2;nin H2;ee;subst;econstructor;ee;au.
ap doubleton_l. ap doubleton_r.
Qed.

Definition union_cond e := forall f, inc f e -> forall g, inc g e -> 
forall x, inc x (domain f) -> inc x (domain g) -> ev f x = ev g x.

Lemma union_cond_rw : union_cond = fun e => 
(forall f g, inc f e -> inc g e -> forall x, inc x (inter2 (domain f) (domain g)) ->
 ev f x = ev g x).
Proof.
ap arrow_extensionality;intros e.
uf union_cond;ap iff_eq;ir.
apply inter2_and in H2;ee;eapply H;try am.
eapply H;try am. ap inter2_inc;am.
Qed.

Lemma union_compatible_axioms : forall e, (forall f, inc f e -> axioms f) -> 
union_cond e -> 
axioms (union e).
Proof.
rw union_cond_rw;ir. uhg;ee;uhg;ir;[|uhg;ir].
apply union_ex in H1;nin H1. ee.
eapply H. am. am.

apply union_ex in H1;apply union_ex in H2;nin H1;nin H2;ee.
assert (y = ev x0 x). ap fun_show_ev. ap H. am. am.
rw H5. assert (y' = ev x1 x). ap fun_show_ev.
ap H;am. am. rw H6. ap H0. am. am. ap inter2_inc.
apply domain_P_in in H4. clpri H4. am. ap H;am.
apply domain_P_in in H3. clpri H3. am. ap H;am.
Qed.

Lemma union_compatible_domain : forall e, (forall f, inc f e -> axioms f) -> 
union_cond e ->
domain (union e) = union (Im domain e).
Proof.
rw union_cond_rw;ir.
ap extensionality;uhg;ir.
apply domain_ev_inc in H1. apply union_ex in H1.
nin H1;ee.
ap union_inc. econstructor;ee.
ap Im_inc. am. ap domain_inc. econstructor;am.
ap union_compatible_axioms;try rw union_cond_rw;am.
apply union_ex in H1;nin H1;ee.
apply Im_ex in H1. nin H1;ee;subst.
ap domain_inc.
apply domain_ev_inc in H2.
econstructor. ap union_inc. econstructor;ee. am. am.
ap H;am.
Qed.

Lemma union_compatible_ev :  forall e, (forall f, inc f e -> axioms f) -> 
union_cond e -> 
forall f, inc f e -> forall x, inc x (domain f) -> ev (union e) x = ev f x.
Proof.
rw union_cond_rw;ir.
assert (inc x (domain (union e))).
rw union_compatible_domain;try am. ap union_inc;econstructor.
ee. ap Im_inc. am. am.
rw union_cond_rw;am.
apply domain_ev_inc in H3. 
assert (axioms (union e)). ap union_compatible_axioms. am. 
rw union_cond_rw;am.
apply H4 with x. am.
ap union_inc;econstructor. ee. am. ap domain_ev_inc. ap H;am. am.
ap union_compatible_axioms;try am. rw union_cond_rw;am.
Qed.

Lemma union_compatible_range : forall e, (forall f, inc f e -> axioms f) -> 
union_cond e ->
range (union e) = union (Im range e).
Proof.
ir. assert (Hcond : union_cond e).
am.
rwi union_cond_rw H0.
ap extensionality;uhg;ir.
apply range_ex in H1. nin H1;ee;subst.
rwi union_compatible_domain H1;try am.
apply union_ex in H1. nin H1;ee.
apply Im_ex in H1. nin H1;ee;subst.
ap union_inc;econstructor. ee.
ap Im_inc. am. ap range_show_inc.
ap H;am. econstructor;ee.
am. 
symmetry. ap union_compatible_ev. am. am.
am. am.
ap union_compatible_axioms;am.

ap range_show_inc.
ap union_compatible_axioms;am.
apply union_ex in H1;nin H1;ee.
apply Im_ex in H1;nin H1;ee;subst.
apply range_ex in H2. nin H2;ee;subst.
econstructor. ee. rw union_compatible_domain. ap union_inc;econstructor.
ee. ap Im_inc. am. am.
am. am.
ap union_compatible_ev. am. am. am. am.
ap H;am.
Qed.

Lemma union_compatible_all : forall e, (forall f, inc f e -> axioms f) -> 
union_cond e ->
(axioms (union e) & domain (union e) = union (Im domain e) & 
(forall f, inc f e -> forall x, inc x (domain f) -> ev (union e) x = ev f x)).
Proof.
ir;ee.
ap union_compatible_axioms;am.
ap union_compatible_domain;am.
ap union_compatible_ev;am.
Qed.

Lemma union_compatible_restr : forall e, (forall f, inc f e -> axioms f) -> 
union_cond e ->
forall f, inc f e -> restr (union e) (domain f) = f.
Proof.
ir. destruct union_compatible_all with e.
am. am.
ee.

ap function_extensionality;au.
ap restr_axioms. am.
rw restr_domain;au.
ap extensionality. ap inter2_r.
uhg;ir. ap inter2_inc;au.
rw H3. ap union_inc. exists (domain f);ee.
ap Im_inc. am. am.

ir. rwi restr_domain H5;au. apply inter2_r in H5.
rw restr_ev;au.
rw H3. ap union_inc. exists (domain f);ee;au.
ap Im_inc;am.
Qed.

Lemma tack_on_axioms : forall f, axioms f -> forall x, ~inc x (domain f) -> forall y,
axioms (tack_on f (J x y)).
Proof.
ir. uhg;ee;uhg;ir;[|uhg;ir].
ir. rwi tack_on_inc H1. nin H1. ap H;am.
subst. ap pair_is_pair.
ir. rwi tack_on_inc H1;rwi tack_on_inc H2;nin H1;nin H2.
eapply H;am.
apply pair_eq in H2. ee.
subst. nin H0.
ap domain_inc. exists y0;am.
apply pair_eq in H1;ee;subst.
nin H0. ap domain_inc. exists y';am.
apply pair_eq in H2;au. apply pair_eq in H1;ee;subst;au.
Qed.

Lemma tack_on_ev_eq : forall f, axioms f -> forall x, ~ inc x (domain f) -> forall y,
ev (tack_on f (J x y)) x = y.
Proof.
ir. symmetry. ap fun_show_ev. ap tack_on_axioms;am.
rw tack_on_inc;au.
Qed.

Lemma tack_on_ev_neq : forall f, axioms f -> forall x, ~ inc x (domain f) -> 
forall z, inc z (domain f) -> forall y, ev (tack_on f (J x y)) z = ev f z.
Proof.
ir;symmetry;ap fun_show_ev. ap tack_on_axioms;am.
rw tack_on_inc;left. ap domain_ev_inc. am. am.
Qed.

Lemma tack_on_domain : forall f x y, domain (tack_on f (J x y)) =
 tack_on (domain f) x.
Proof.
ir. ap extensionality;uhg;ir.
rw tack_on_inc.
apply Z_pr in H. nin H.
rwi tack_on_inc H;nin H.
left. ap domain_inc. exists x0;am.
apply pair_eq in H;ee;subst.
au.
rwi tack_on_inc H;nin H;subst.
ap domain_inc. apply Z_pr in H. nin H.
exists x0;rw tack_on_inc;au.
ap domain_inc. exists y;rw tack_on_inc;au.
Qed.

End Function.

Module Map.
Import Function.

Definition is_map a b f := 
and (Function.axioms f)
(and (domain f = a)
(sub (range f) b)).

Lemma map_extensionality : forall a b f, is_map a b f -> forall g, is_map a b g -> 
(forall x, inc x a -> ev f x = ev g x) -> f=g.
Proof.
ir. ap function_extensionality. am. am.
transitivity a. am. symmetry;am.
replace (domain f) with a. am.
symmetry;am.
Qed.

Lemma map_sub : forall a b f, is_map a b f -> forall a' b' f', sub a a' -> 
is_map a' b' f' -> (forall x, inc x a -> ev f' x = ev f x) -> sub f f'.
Proof.
ir. ap function_sub;try am.
replace (domain f) with a. replace (domain f') with a'. am.
symmetry;am. symmetry;am.
replace (domain f) with a. am.
symmetry;am.
Qed.

Lemma trans_of_map : forall a b f, is_map a b f -> 
Application.axioms a b (ev f).
Proof.
ir;uhg;ir.
ap H. ap range_ev_inc. am.
uh H;ee. rw H1. am.
Qed.

Lemma map_of_trans : forall a b f, Application.axioms a b f -> 
is_map a b (create a f).
Proof.
ir.
uhg;ee. ap create_axioms.
ap create_domain.
uhg;ir. rewrite create_range in H0. apply Im_ex in H0. nin H0. ee.
subst.
ap H;am.
Qed.

Lemma axioms_map : forall f, axioms f -> is_map (domain f) (range f) f.
Proof.
ir. uhg;ee. am. tv. ap sub_refl.
Qed.

Definition injective a b f := is_map a b f & (Application.injects a (ev f)).
Definition surjective a b f := is_map a b f & (Application.covers a b (ev f)).
Definition bijective a b f := is_map a b f & (Application.injects a (ev f))
&  (Application.covers a b (ev f)).

Lemma bijective_injective : forall a b f, bijective a b f -> injective a b f.
Proof.
ir;uhg;ee;am.
Qed.

Lemma bijective_surjective : forall a b f, bijective a b f -> surjective a b f.
Proof.
ir;uhg;ee;am.
Qed. 

Lemma surjective_range : forall a b f, surjective a b f -> range f = b.
Proof.
ir. ap extensionality. am.
uhg;ir.
ap range_show_inc. am.
cp H0. apply H in H1. nin H1;ee. exists x. ee.
uh H;ee;uh H;ee. rw H4. am. am.
Qed.

Lemma bijective_rw : forall a b f, bijective a b f = and (injective a b f) (surjective a b f).
Proof.
ir;ap iff_eq;ir;ee;uhg;ee;am.
Qed.

Lemma surjective_range_rw : forall a b f, surjective a b f = 
and (is_map a b f) (range f = b).
Proof.
ir. ap iff_eq;ir.
ee. am.
eapply surjective_range. am.
ee. uhg;ee. am.
wr H0. uhg;ir.
apply range_ex in H1. uh H;ee. rwi H2 H1.
nin H1. exists x;ee;au.
am.
Qed.

Lemma range_surjective : forall a b f, is_map a b f -> range f = b -> 
surjective a b f.
Proof.
ir;rw surjective_range_rw;ee;am.
Qed.

Lemma range_bijective : forall a b f, injective a b f -> range f = b -> 
bijective a b f.
Proof.
ir;rw bijective_rw;ee. am. ap range_surjective;am.
Qed.

Definition map_set a b := Z (powerset (product a b)) (fun f => is_map a b f).

Lemma map_set_map : forall a b f, inc f (map_set a b) -> is_map a b f.
Proof.
ir.
eapply Z_pr. am.
Qed.

Lemma map_map_set : forall a b f, is_map a b f -> inc f (map_set a b).
Proof.
ir.
ap Z_inc.
ap powerset_inc. uhg;ir.
cp H0. apply H in H0. nin H0. uh H;ee.
ap product_pair_inc.
wr H0. ap domain_inc. exists b0;am.
ap H2. ap range_inc. exists a0;am.
am.
Qed.

Lemma map_set_rw : forall a b f, inc f (map_set a b) = is_map a b f.
Proof.
ir;ap iff_eq.
ap map_set_map. ap map_map_set.
Qed.

Lemma map_to_sub : forall b b', sub b b' -> forall a f, is_map a b f -> is_map a b' f.
Proof.
ir. uhg;ee;au.
apply sub_trans with b;am.
Qed.

Lemma injective_sub : forall b b', sub b b' -> forall a f, injective a b f ->
 injective a b' f.
Proof.
ir. uhg;ee.
apply map_to_sub with b;am. am.
Qed.

Lemma id_map : forall a, is_map a a (id a).
Proof.
ir. uhg;ee.
ap id_axioms. ap id_domain. rw id_range. ap sub_refl.
Qed.

Lemma id_injective : forall a, injective a a (id a).
Proof.
ir. uhg;ee. ap id_map.
uhg;ir. rwi id_ev H1;au. rwi id_ev H1;au.
Qed.

Lemma id_surjective : forall a, surjective a a (id a).
Proof.
ir. uhg;ee. ap id_map.
uhg;ir.
exists y;ee. am. ap id_ev. am.
Qed.

Lemma id_bijective : forall a, bijective a a (id a).
Proof.
ir. rw bijective_rw. ee.
ap id_injective.
ap id_surjective.
Qed.

(*needs choice*)
Definition inverse f := create (range f)
 (fun y => choose (fun x => inc x (domain f) & y = ev f x)).

Lemma inverse_axioms : forall f, axioms (inverse f).
Proof.
ir;ap create_axioms.
Qed.

Lemma inverse_domain : forall f, domain (inverse f) = range f.
Proof.
ir;ap create_domain.
Qed.

Lemma inverse_ev_pr : forall f, axioms f -> forall y, inc y (range f) -> 
(inc (ev (inverse f) y) (domain f) & y = ev f (ev (inverse f) y)).
Proof.
ir.
uf inverse. rw create_ev.
ap choose_pr. apply range_ex in H0. am. am.
am.
Qed.

Lemma inverse_range_sub : forall f, axioms f -> sub (range (inverse f)) (domain f).
Proof.
ir. uhg;ir.
apply range_ex in H0. nin H0;ee;subst.
ap inverse_ev_pr. am.
wr inverse_domain. am.
ap inverse_axioms.
Qed.

Lemma inverse_ev_r : forall f, axioms f -> forall y, inc y (range f) -> 
y = ev f (ev (inverse f) y).
Proof.
ir;ap inverse_ev_pr. am. am.
Qed.

Lemma surjective_inverse_map : forall a b f, surjective a b f -> 
is_map b a (inverse f).
Proof.
ir. uhg;ee.
ap inverse_axioms.
rw inverse_domain. eapply surjective_range. am.

uh H;ee;uh H;ee.
wr H1. ap inverse_range_sub. am.
Qed.

Lemma inverse_injects : forall f, axioms f ->
 Application.injects (range f) (ev (inverse f)).
Proof.
uhg. ir.
rw (inverse_ev_r H H0). rw (inverse_ev_r H H1).
rw H2. tv.
Qed.

Lemma surjective_inverse_injective : forall a b f, surjective a b f ->
 injective b a (inverse f).
Proof.
uhg. ir;ee. ap surjective_inverse_map. am.
rwi surjective_range_rw H. ee;subst.
ap inverse_injects. am.
Qed.

Definition inverseT a b f g := 
and (forall x, inc x a -> g (f x) = x)
(forall y, inc y b -> f (g y) = y).

Lemma inverseT_sym : forall a b f g, inverseT a b f g -> inverseT b a g f.
Proof.
uf inverseT;ir;ee;am.
Qed.

Definition are_inverse a b f g := 
and (is_map a b f)
(and (is_map b a g)
(inverseT a b (ev f) (ev g))).

Lemma are_inverse_sym : forall a b f g, are_inverse a b f g -> are_inverse b a g f.
Proof.
uf are_inverse;ir;ee;try am. ap inverseT_sym;am.
Qed.

Lemma are_inverse_bijective : forall a b f g, are_inverse a b f g -> bijective a b f.
Proof.
ir.
uh H;ee. uh H1;ee.
uhg;ee. am.
uhg;ir.
cp (uneq (ev g) H5).
rwi H1 H6. rwi H1 H6. am. am. am.
uhg;ir.
exists (ev g y). ee. eapply trans_of_map;am. ap H2. am.
Qed.

Lemma inverseT_bijective : forall a b f g, Application.axioms a b f -> 
Application.axioms b a g -> inverseT a b f g -> 
Application.bijective a b f.
Proof.
ir. uhg;ee. am.
uhg;ir.
cp (uneq g H4).
uh H1;ee. rwi H1 H5. rwi H1 H5. am. am. am.
uhg;ir.
uh H1;ee.
econstructor;ee. ap H0. am.
ap H3;am.
Qed. (*need both axioms for bijective + covers*)

Lemma are_inverse_bijective_both : forall a b f g, are_inverse a b f g ->
and (bijective a b f) (bijective b a g).
Proof.
ir;ee.
eapply are_inverse_bijective. am.
eapply are_inverse_bijective. ap are_inverse_sym. am.
Qed.

Lemma bijective_inverse_of : forall a b f, bijective a b f -> 
are_inverse a b f (inverse f).
Proof.
ir. uhg;ee.
am.
uhg;ee. ap inverse_axioms.
rw inverse_domain. rwi bijective_rw H. rwi surjective_range_rw H.
am.
uh H;ee;uh H;ee. wr H2.
ap inverse_range_sub. am.
uhg;ee.
ir. ap H.
eapply trans_of_map. eapply surjective_inverse_map. rwi bijective_rw H;am.
eapply trans_of_map;am.
am.
wr inverse_ev_r. tv. am. ap range_ev_inc. am. uh H;ee;uh H;ee. rw H3;am.
ir.
symmetry. ap inverse_ev_r. am.
rwi bijective_rw H;rwi surjective_range_rw H. ee. rw H2;am.
Qed.

Lemma bijective_eq_inverse : forall a b f, bijective a b f = ex (are_inverse a b f).
Proof.
ir. ap iff_eq; ir.
exists (inverse f). ap bijective_inverse_of. am.
nin H. eapply are_inverse_bijective. am.
Qed.

Lemma inverse_unicity : forall a b f g, are_inverse a b f g ->
 forall g', are_inverse a b f g' -> 
g=g'.
Proof.
ir. uh H;ee;uh H0;ee.
ap function_extensionality;au.
etransitivity;au. symmetry;am.
ir.

replace (domain g) with b in H5.
assert (x = ev f (ev g x)).
symmetry. ap H2. am.
rw H6.
uh H2;uh H4;ee. rw H2. rw H4. tv. 
eapply trans_of_map;am. eapply trans_of_map;am.
symmetry;am.
Qed.

Lemma id_inverse : forall a, are_inverse a a (id a) (id a).
Proof.
ir.
uhg;ee.
ap id_map. ap id_map.
uhg;ee;ir;repeat rw id_ev;try am. tv. tv.
Qed.

Lemma bijective_inverse_bijective : forall a b f, bijective a b f -> 
bijective b a (inverse f).
Proof.
ir. apply bijective_inverse_of in H. apply are_inverse_bijective_both in H.
am.
Qed.

Lemma bijective_range : forall a b f, bijective a b f -> range f = b.
Proof.
ir;rwi bijective_rw H;rwi surjective_range_rw H. am.
Qed.

Lemma map_composable : forall a b c f g, is_map a b f -> is_map b c g -> 
composable g f.
Proof.
ir. uh H;uh H0;ee;subst.
uhg;ee.
am. am.
am.
Qed.

Lemma map_compose : forall a b c f g, is_map a b f -> is_map b c g -> 
is_map a c (compose g f).
Proof.
ir.
assert (Hc : composable g f). eapply map_composable. am. am.
 uh H;uh H0;ee;subst.
uhg;ee. ap compose_axioms.
rw composable_domain. tv.
uhg;ee;au.
uhg;ir.
apply range_ex in H1. nin H1;ee.
rwi composable_domain H1.
subst. ap H2. rw compose_ev.
ap range_ev_inc. am.
ap H4. ap range_ev_inc. am. am.
rw composable_domain. am.
am. am.
ap compose_axioms.
Qed.

Lemma map_compose_rw : forall a b c f g, is_map a b f -> is_map b c g -> 
compose g f = L a (fun x => ev g (ev f x)).
Proof.
ir.
cp (map_composable H H0).
 ap function_extensionality.
ap compose_axioms. ap create_axioms.
rw create_domain. etransitivity. 
ap composable_domain. am. am.
ir. assert (domain (compose g f) =  a).
Focus 2. rwi H3 H2.
rw create_ev. ap compose_ev.
rw H3;am.
am.
rw composable_domain;am.
Qed.

Lemma map_compose_ev : forall a b c f g, is_map a b f -> is_map b c g -> 
forall x, inc x a -> ev (compose g f) x = ev g (ev f x).
Proof.
ir. erewrite map_compose_rw. etransitivity. ap create_ev.
am. tv.
am. am.
Qed.

Lemma map_compose_assoc : forall a b f, is_map a b f -> 
forall c g, is_map b c g -> 
forall d h, is_map c d h -> 
compose h (compose g f) = compose (compose h g) f.
Proof.
ir.
rw (map_compose_rw (map_compose H H0) H1).
rw (map_compose_rw H H0).
rw (map_compose_rw H (map_compose H0 H1)).
rw (map_compose_rw H0 H1).
ap create_extensionality;ir.
repeat rw create_ev;au.
eapply trans_of_map;am.
Qed.

Lemma map_compose_id_r : forall a b f, is_map a b f -> 
compose f (id a) = f.
Proof.
ir. erewrite map_compose_rw.
Focus 2. ap id_map.
Focus 2. am.
ap function_extensionality.
ap create_axioms. am.
rw create_domain;symmetry;am.
rw create_domain. ir.
rw create_ev. rw id_ev. tv. am. am.
Qed.

Lemma map_compose_id_l : forall a b f, is_map a b f -> 
compose (id b) f = f.
Proof.
ir. erewrite map_compose_rw.
Focus 3. ap id_map.
Focus 2. am.
ap function_extensionality.
ap create_axioms. am.
rw create_domain;symmetry;am.
rw create_domain. ir.
rw create_ev. rw id_ev. tv. eapply trans_of_map;am. am.
Qed.

Lemma bijective_inverse_compose_r : forall a b f, bijective a b f -> 
compose f (inverse f) = id b.
Proof.
ir. ap function_extensionality.
ap compose_axioms. ap id_axioms.
rw id_domain. rw composable_domain. rw inverse_domain.
apply bijective_range with a;am.
eapply map_composable. ap bijective_inverse_bijective. am. am.
ir.
cp (bijective_inverse_of H).
 rwi composable_domain H0. rwi inverse_domain H0. 
rwi (bijective_range H) H0. rw compose_ev.
rw id_ev. ap H1. am. am.
rw composable_domain. rw inverse_domain. erewrite bijective_range. ap H0.
am. eapply map_composable. ap bijective_inverse_bijective. am.
am. eapply map_composable. ap bijective_inverse_bijective. am.
am.
Qed.

Lemma bijective_inverse_compose_l :  forall a b f, bijective a b f -> 
compose (inverse f) f = id a.
Proof.
ir.
assert (composable (inverse f) f). eapply map_composable. am.
ap bijective_inverse_bijective;am.
cp (composable_domain H0). replace (domain f) with a in H1.
ap function_extensionality. ap compose_axioms. ap id_axioms.
rw id_domain. am.
ir. rwi H1 H2. rw compose_ev. rw id_ev. cp (bijective_inverse_of H).
uh H3;ee. uh H5;ee. ap H5. am. am. rw H1;am.
uh H;ee. symmetry;ap H.
Qed.

Lemma bijective_inverse_ev_l : forall a b f, bijective a b f -> forall x, 
inc x a -> ev (inverse f) (ev f x) = x.
Proof.
ir. wr compose_ev. rw (bijective_inverse_compose_l H). ap id_ev;am.
rw composable_domain. replace( domain f) with a. am. symmetry;uh H;ee;ap H.
eapply map_composable;try am. ap bijective_inverse_bijective;am.
Qed.

Lemma bijective_inverse_ev_r : forall a b f, bijective a b f -> forall x, 
inc x b -> ev f (ev (inverse f) x) = x.
Proof.
ir. wr compose_ev. rw (bijective_inverse_compose_r H). ap id_ev;am.
rw composable_domain. 
rw inverse_domain. erewrite bijective_range;am.
eapply map_composable;try am. ap bijective_inverse_bijective;am.
Qed.


Definition are_equipotent a b := exists f, bijective a b f.

Lemma are_equipotent_refl : forall a, are_equipotent a a.
Proof.
ir. exists (id a). ap id_bijective.
Qed.

Lemma are_equipotent_sym : forall a b, are_equipotent a b -> are_equipotent b a.
Proof.
ir.
nin H.
exists (inverse x).
ap bijective_inverse_bijective. am.
Qed.

Lemma injective_compose : forall a b c f g, injective a b f -> injective b c g -> 
injective a c (compose g f).
Proof.
ir.
uhg;ee.
eapply map_compose. am. am.
uh H;ee;uh H0;ee.
cp ( map_composable H H0).
uhg;ir.
rwi compose_ev H6. rwi compose_ev H6.
apply H2 in H6. ap H1.
am. am. am.
uh H;uh H0;ee; subst.
ap H10. ap range_ev_inc. am. am.

uh H;uh H0;ee; subst.
ap H10. ap range_ev_inc. am. am.

rw composable_domain;au.
uh H;ee;subst. am.
rw composable_domain;au;uh H;ee;subst;am.
Qed.

Lemma surjective_compose : forall a b c f g, surjective a b f -> surjective b c g -> 
surjective a c (compose g f).
Proof.
intros a b c f g. repeat rw surjective_range_rw.
ir;ee. eapply map_compose;am.
subst. uh H;ee;uh H0;ee;subst.
ap extensionality;uhg;ir.
apply range_ex in H1. nin H1;ee;subst.
rw compose_ev. ap range_ev_inc. am.
rwi composable_domain H1. rw H3. ap range_ev_inc. am. am.
uhg;ee;au. rw H3;ap sub_refl.
am.
ap compose_axioms.
apply range_ex in H1. nin H1;ee;subst.
rwi H3 H1. apply range_ex in H1. nin H1;ee. subst.
ap range_show_inc. ap compose_axioms. exists x0.
ee. rw composable_domain.
am.
uhg;ee;au. rw H3;ap sub_refl.
ap compose_ev. rw composable_domain. am.
uhg;ee;au;rw H3;ap sub_refl.
am. am.
Qed.

Lemma bijective_compose : forall a b c f g, bijective a b f -> bijective b c g -> 
bijective a c (compose g f).
Proof.
intros a b c f g. repeat rw bijective_rw.
ir;ee. eapply injective_compose;am. eapply surjective_compose;am.
Qed.

Lemma are_equipotent_trans : forall a b c, are_equipotent a b ->
 are_equipotent b c -> are_equipotent a c.
Proof.
ir.
nin H;nin H0. econstructor.
eapply bijective_compose;am.
Qed.

Lemma map_of_bijective : forall a b f, Application.bijective a b f ->
 bijective a b (create a f).
Proof.
ir. uh H;ee.
uhg;ee.
ap map_of_trans. am.
uhg;ir.
ap H0. am. am. rwi create_ev H4;au;rwi create_ev H4;au.

uhg;ir. cp H2. apply H1 in H3. nin H3. ee;subst.
exists x;ee. am.
ap create_ev;am.
Qed.

Lemma bijective_of_map : forall a b f, bijective a b f -> Application.bijective a b (ev f).
Proof.
ir;uhg;ee.
ap trans_of_map. am.
am. am.
Qed.

Lemma are_equipotent_transformation : forall a b, are_equipotent a b =
 (ex (Application.bijective a b)).
Proof.
ir;ap iff_eq;ir;nin H.
exists (ev x). ap bijective_of_map. am.
exists (Function.create a x). ap map_of_bijective. am.
Qed.

Lemma trans_equipotent : forall a b, ex (Application.bijective a b) ->
 are_equipotent a b.
Proof.
ir;rw are_equipotent_transformation. am.
Qed.

Lemma map_set_curry : forall a b c, are_equipotent (map_set (product b c) a)
 (map_set c (map_set b a)).
Proof.
ir. rw are_equipotent_transformation.
exists (fun f => L c (fun x => L b (fun y => ev f (J y x)))).
uhg;ee;uhg;ir.
rw map_set_rw. ap map_of_trans.
uhg;ir. rw map_set_rw. ap map_of_trans.
uhg;ir. rwi map_set_rw H. eapply trans_of_map.
am. ap product_pair_inc;am.
rwi map_set_rw H;rwi map_set_rw H0.
ap function_extensionality;try am.
uh H0;ee. rw H2. am.
ir. uh H;ee. rwi H3 H2.
apply product_pr in H2;ee. nin H2. clpri H5;clpri H6.
transitivity (ev (ev  (L c (fun x0 : E => L b (fun y : E => ev x (J y x0)))) b0) a0).
rw create_ev. rw create_ev. tv. am. am.
rw H1.
rw create_ev. rw create_ev. tv. am. am.

rwi map_set_rw H.
exists (L (product b c) (fun p => ev (ev y (Q p)) (P p))).
ee. rw map_set_rw.
ap map_of_trans. uhg;ir.
apply product_pr in H0;ee;nin H0. clpri H1;clpri H2.
clpr. eapply trans_of_map. wr map_set_rw. eapply trans_of_map. am.
am. am.

ap function_extensionality. ap create_axioms. am.
rw create_domain. symmetry;am.
ir.
rwi create_domain H0.
rw create_ev. cp (trans_of_map H). cp (H1 x H0).
clear H1.
rwi map_set_rw H2.
ap function_extensionality. ap create_axioms. am.
rw create_domain. symmetry;am.
rw create_domain. ir.
rw create_ev. rw create_ev. clpr.
tv.
ap product_pair_inc;am. am. am.
Qed.

Lemma map_of_injective : forall a b f, Application.injective a b f ->
 injective a b (create a f).
Proof.
ir. uh H;ee.
uhg;ee.
ap map_of_trans. am.
uhg;ir.
ap H0. am. am. rwi create_ev H3;au;rwi create_ev H3;au.
Qed.

Lemma injective_of_map : forall a b f, injective a b f ->
 Application.injective a b (ev f).
Proof.
ir;uhg;ee.
ap trans_of_map. am.
am.
Qed.

Lemma map_of_surjective : forall a b f, Application.surjective a b f ->
 surjective a b (create a f).
Proof.
ir. uh H;ee.
uhg;ee.
ap map_of_trans. am.
uhg;ir. cp H1. apply H0 in H2. nin H2. ee;subst.
exists x;ee. am.
ap create_ev;am.
Qed.

Lemma surjective_of_map : forall a b f, surjective a b f ->
 Application.surjective a b (ev f).
Proof.
ir;uhg;ee.
ap trans_of_map. am.
am.
Qed.


Lemma tack_on_map : forall a b f, is_map a b f -> forall x, ~inc x a -> forall y, 
is_map (tack_on a x) (tack_on b y) (tack_on f (J x y)).
Proof.
ir. uh H;ee. subst.
uhg;ee. ap tack_on_axioms;am.
ap tack_on_domain.
uhg;ir.
apply range_ex in H1. nin H1;ee;subst.
rwi tack_on_domain H1. rwi tack_on_inc H1;nin H1;subst.
rw tack_on_inc;left. ap H2. rw tack_on_ev_neq. ap range_ev_inc.
am. am. am. am. am.
rw tack_on_inc;right. rw tack_on_ev_eq;au.
ap tack_on_axioms;am.
Qed.

Lemma map_tack_on_ev_eq : forall a b f, is_map a b f -> 
forall x, ~inc x a -> forall y, ev (tack_on f (J x y)) x = y.
Proof.
ir. ap tack_on_ev_eq. am. uhg;ir. ap H0.
eapply eq_ind. am. am.
Qed.

Lemma map_tack_on_ev : forall a b f, is_map a b f ->
forall x, ~inc x a -> forall z, inc z a -> forall y, ev (tack_on f (J x y)) z = ev f z.
Proof.
ir. ap tack_on_ev_neq. am. uhg;ir;ap H0;eapply eq_ind;am.
eapply eq_ind;try am. symmetry;am.
Qed.

Lemma tack_on_injective : forall a b f, injective a b f -> forall x, ~inc x a -> 
forall y, ~inc y b -> injective (tack_on a x) (tack_on b y) (tack_on f (J x y)).
Proof.
ir. uhg;ee. ap tack_on_map. am. am.
uhg;ir.
rwi tack_on_inc H2;rwi tack_on_inc H3;nin H2;nin H3;subst.
rwi (map_tack_on_ev (and_P H)) H4;au. rwi (map_tack_on_ev (and_P H)) H4;au.
ap H;am.
rwi (map_tack_on_ev (and_P H)) H4;au. rwi (map_tack_on_ev_eq (and_P H)) H4;au.
nin H1. wr H4. eapply trans_of_map. am. am.
rwi (map_tack_on_ev_eq (and_P H)) H4;au. rwi (map_tack_on_ev (and_P H)) H4;au.
nin H1. rw H4. eapply trans_of_map. am. am.
tv.
Qed.

Lemma tack_on_surjective : forall a b f, surjective a b f -> forall x, ~ inc x a -> 
forall y, surjective (tack_on a x) (tack_on b y) (tack_on f (J x y)).
Proof.
ir;uhg;ee. ap tack_on_map;am.
uhg;ir.
rwi tack_on_inc H1;nin H1;subst.
apply H in H1. nin H1;ee;subst.
exists x0;ee. rw tack_on_inc;au.
rw (map_tack_on_ev (and_P H)). tv. am. am.
exists x;ee. rw tack_on_inc. au.
eapply map_tack_on_ev_eq. am. am.
Qed.

Lemma tack_on_bijective : forall a b f, bijective a b f -> forall x, ~inc x a -> 
forall y, ~inc y b -> bijective (tack_on a x) (tack_on b y) (tack_on f (J x y)).
Proof.
ir. rw bijective_rw. rwi bijective_rw H;ee.
ap tack_on_injective;am.
ap tack_on_surjective;am.
Qed.

Lemma bijective_inverseT : forall a b f, Application.bijective a b f -> exists g, 
Application.bijective b a g & inverseT a b f g.
Proof.
ir.
cp (map_of_bijective H).
cp (bijective_inverse_of H0).
exists (ev (inverse (L a f))). ee.
ap bijective_of_map. ap bijective_inverse_bijective. am.
uh H1;ee.
uhg;ee;ir. etransitivity. Focus 2. uh H3;ee. ap H3. am.
rw create_ev;au.

etransitivity. Focus 2. ap H3. am.
rw create_ev;au.
eapply trans_of_map. am. am.
Qed.

Lemma tack_on_equipotent : forall x y a b, ~inc a x -> ~ inc b y ->
are_equipotent x y = are_equipotent (tack_on x a) (tack_on y b).
Proof.
ir;ap iff_eq;ir.
nin H1. cp (bijective_of_map H1).
assert (Application.bijective (tack_on x a) (tack_on y b) (fun z => 
if eq_dec z a then b else ev x0 z)).
uhg;ee;uhg;ir.
rwi tack_on_inc H3;nin H3. rw eq_dec_if_not.
rw tack_on_inc;left. ap H2. am.
uhg;ir;subst. au.
subst. rw eq_dec_if. rw tack_on_inc;au.
rwi tack_on_inc H3;rwi tack_on_inc H4;nin H3;nin H4;subst.
rwi eq_dec_if_not H5. rwi eq_dec_if_not H5.
ap H2;am.
uhg;ir;subst. au.
uhg;ir;subst;au.
rwi eq_dec_if H5. rwi eq_dec_if_not H5.
nin H0. wr H5. ap H2. am.
uhg;ir. ap H. wr H4. am.
rwi eq_dec_if H5. rwi eq_dec_if_not H5.
nin H0. rw H5. ap H2. am.
uhg;ir. ap H. wr H3. am.
tv.

rwi tack_on_inc H3;nin H3.
apply H2 in H3. nin H3;ee;subst.
exists x1;ee. rw tack_on_inc;au.
rw eq_dec_if_not. tv. uhg;ir;subst;au.
subst. exists a;ee. rw tack_on_inc;au.
rw eq_dec_if. tv.
econstructor. ap map_of_bijective. am.

nin H1. cp (bijective_of_map H1).
assert (inc b (tack_on y b)). rw tack_on_inc;au.
apply H1 in H3. nin H3;ee.
subst.
rwi tack_on_inc H3;nin H3.
assert (inc (ev x0 a) (tack_on y (ev x0 x1))). ap H2.
rw tack_on_inc;au.
rwi tack_on_inc H4;nin H4.
Focus 2. apply H2 in H4. subst.
nin H;am.
rw tack_on_inc;au. rw tack_on_inc;au.

assert (Application.bijective x y (fun z => if eq_dec z x1 then ev x0 a else
ev x0 z)).
uhg;ee;uhg;ir.
nin (eq_dec x2 x1). am.
assert (inc (ev x0 x2) (tack_on y (ev x0 x1))). ap H2. rw tack_on_inc;au.
rwi tack_on_inc H6;nin H6. am.
nin b. ap H2. rw tack_on_inc;au. rw tack_on_inc;au.
am.

assert (forall j k, sub j (tack_on j k)).
uhg;ir;rw tack_on_inc;au.

nin (eq_dec x2 x1);nin (eq_dec y0 x1).
subst. tv.
apply H2 in H7;au. subst. nin H;am.
rw tack_on_inc;au. ap H8. am.
subst. 
apply H2 in H7 ;au. subst. nin H;am.
ap H8;am. rw tack_on_inc;au.
ap H2;au. ap H8;am. ap H8;am.

nin (eq_dec y0 (ev x0 a)).
subst. exists x1;ee;au. rw eq_dec_if;tv.
assert (inc y0 (tack_on y (ev x0 x1))).
rw tack_on_inc;au.
apply H2 in H6. nin H6;ee;subst.
rwi tack_on_inc H6;nin H6.
exists x2;ee. am. rw eq_dec_if_not. tv.
uhg;ir;subst. ap H0;am.
subst. nin b;tv.
econstructor;ap map_of_bijective;am.

subst.
assert (Application.bijective x y (ev x0)).
uhg;ee;uhg;ir.
assert (inc x1 (tack_on x a)). rw tack_on_inc;au.
apply H2 in H4. rwi tack_on_inc H4;nin H4;au.
nin H. apply H2 in H4;au.
subst;au. rw tack_on_inc;au. rw tack_on_inc;au.
ap H2;au. rw tack_on_inc;au. rw tack_on_inc;au.

assert (inc y0 (tack_on y (ev x0 a))).
rw tack_on_inc;au. apply H2 in H4;nin H4;ee.
subst. rwi tack_on_inc H4;nin H4. exists x1;ee. am.
tv.
subst. nin H0;am.
econstructor;ap map_of_bijective;am.
Qed.

Lemma transfo_bijective_compose : forall a b c f g, Application.bijective a b f ->
 Application.bijective b c g -> 
Application.bijective a c (fun x => g (f x)).
Proof.
ir. uhg;ee;uhg;ir.
ap H0;ap H;am.
ap H. am. am. ap H0;au. ap H;am. ap H;am.
cp H1. apply H0 in H2. nin H2;ee.
apply H in H2. nin H2;ee;subst. exists x0;ee;au.
Qed.

Lemma union2_map : forall a b f a' b' g, is_map a b f -> is_map a' b' g -> 
inter2 a a' = emptyset -> is_map (union2 a a') (union2 b b') (union2 f g).
Proof.
ir.
uh H;ee;uh H0;ee. wri H2 H1;wri H4 H1.
uhg;ee.
ap union2_axioms;am. wr H2;wr H4. ap union2_domain;am.
rw union2_range;try am.

uhg;ir.
apply union2_or in H6. ap union2_inc. nin H6;au.
Qed.

Lemma union2_injective : forall a b f a' b' g, injective a b f -> injective a' b' g -> 
inter2 a a' = emptyset -> inter2 (range f) (range g) = emptyset ->
 injective (union2 a a') (union2 b b') (union2 f g).
Proof.
ir. uhg;ee.
ap union2_map;am.
uhg;ir.
assert (inter2 (domain f) (domain g) = emptyset).
uh H;uh H0;ee;uh H;uh H0;ee.
rw H10;rw H8. am.
apply union2_or in H3;apply union2_or in H4.
nin H3;nin H4.
rwi union2_ev_l H5. rwi union2_ev_l H5.
ap H. am. am. am.
am. am. am. uh H;ee. uh H;ee. rw H8;am.
am. am. am. uh H;ee. uh H;ee;rw H8;am.

assert (domain f = a). uh H;ee. ap H.
subst. assert (domain g = a'). uh H0;ee;ap H0. subst.
rwi union2_ev_l H5. rwi union2_ev_r H5.
ap False_rect. eapply emptyset_empty. wr H2.
ap inter2_inc. ap range_ev_inc. am. am. rw H5. ap range_ev_inc. am. am.
am. am. am. am. am. am. am. am.

assert (domain f = a). uh H;ee. ap H.
subst. assert (domain g = a'). uh H0;ee;ap H0. subst.
rwi union2_ev_r H5. rwi union2_ev_l H5.
ap False_rect. eapply emptyset_empty. wr H2.
ap inter2_inc. ap range_ev_inc. am. am. wr H5. ap range_ev_inc. am. am.
am. am. am. am. am. am. am. am.

assert (domain f = a). uh H;ee. ap H.
subst. assert (domain g = a'). uh H0;ee;ap H0. subst.
rwi union2_ev_r H5;try am. rwi union2_ev_r H5;try am.
ap H0. am. am. am.
Qed.

Lemma union2_fast_injective :  forall a b f a' b' g, injective a b f -> injective a' b' g -> 
inter2 a a' = emptyset -> inter2 b b' = emptyset ->
 injective (union2 a a') (union2 b b') (union2 f g).
Proof.
ir. ap union2_injective;try am.
ap empty_emptyset.
ir. 
eapply emptyset_empty. wr H2. apply inter2_and in H3;ee.
ap inter2_inc;au. ap H. am. ap H0;am.
Qed.

Lemma union2_surjective : forall a b f a' b' g, surjective a b f -> surjective a' b' g -> 
inter2 a a' = emptyset -> surjective (union2 a a') (union2 b b') (union2 f g).
Proof.
intros a b f a' b' g.
repeat rw surjective_range_rw. ir;ee.
ap union2_map;am.
subst. ap union2_range.
am. am.
replace (domain f) with a;try am. wr H1. ap uneq. am. symmetry;am.
Qed.

Lemma union2_bijective : forall a b f a' b' g, bijective a b f -> bijective a' b' g -> 
inter2 a a' = emptyset -> inter2 (range f) (range g) = emptyset ->
 bijective (union2 a a') (union2 b b') (union2 f g).
Proof.
intros until 0.
repeat rw bijective_rw. ir;ee;[ap union2_injective | ap union2_surjective];am.
Qed.

Lemma union2_fast_bijective : forall a b f a' b' g, bijective a b f -> bijective a' b' g -> 
inter2 a a' = emptyset -> inter2 b b' = emptyset ->
 bijective (union2 a a') (union2 b b') (union2 f g).
Proof.
intros until 0.
repeat rw bijective_rw. ir;ee;[ap union2_fast_injective | ap union2_surjective];am.
Qed.

Definition iso_sub a b := exists x, are_equipotent a x & sub x b .

Lemma iso_sub_rw : forall a b, iso_sub a b = exists f, injective a b f.
Proof.
ir;ap iff_eq;ir.
nin H. ee. nin H.
exists x0. uhg;ee. uhg;ee. am. uh H;ee. ap H.
apply sub_trans with x. am. am. am.
nin H. exists (range x). ee. Focus 2. am.
exists x. rw bijective_rw. rw surjective_range_rw.
assert (is_map a (range x) x). uhg;ee. am. uh H;ee;ap H. ap sub_refl.
ee. uhg;ee. am. am.
am. tv.
Qed.

Definition iso_sub_strict a b := and (iso_sub a b) (~are_equipotent a b).

Lemma iso_sub_refl : forall a, iso_sub a a.
Proof.
ir;rw iso_sub_rw. exists (id a). ap id_injective.
Qed.

Lemma sub_iso_sub : forall a b, sub a b -> iso_sub a b.
Proof.
ir. uhg. exists a;ee;au.
ap are_equipotent_refl.
Qed.

Lemma iso_strict_irrefl : forall a, ~iso_sub_strict a a.
Proof.
ir;uhg;ir. ap H. ap are_equipotent_refl.
Qed.

Lemma iso_sub_trans : forall a b, iso_sub a b -> forall c, iso_sub b c -> iso_sub a c.
Proof.
ir. rwi iso_sub_rw H;rwi iso_sub_rw H0;rw iso_sub_rw.
nin H;nin H0. econstructor.
eapply injective_compose. am. am.
Qed.

Lemma Im_iso_sub : forall x f, iso_sub (Im f x) x.
Proof.
ir. assert (Application.surjective x (Im f x) f).
uhg;ee;uhg;ir. ap Im_inc;am. Im_nin H. subst;exists x0;ee;au.
assert (ex (Application.surjective x (Im f x))). exists f;am.
apply Application.surjective_injective_back in H0.
nin H0.
rw iso_sub_rw. econstructor. ap map_of_injective. am.
Qed.

Lemma cantor_bernstein : forall s t, iso_sub s t -> iso_sub t s ->
 are_equipotent s t.
Proof.
ir. rwi iso_sub_rw H.
rwi iso_sub_rw H0. destruct H as [f H];destruct H0 as [g H0].
assert (Application.axioms s t (ev f) & Application.axioms t s (ev g)).
ee;eapply trans_of_map;am.
ee.

pose (cs := create (powerset s) (complement s)).
assert (Application.axioms (powerset s) (powerset s) (complement s)).
uhg;ir. ap powerset_inc. ap Z_sub. cp (map_of_trans H3).
pose (ct := create (powerset t) (complement t)).
assert (Application.axioms (powerset t) (powerset t) (complement t)).
uhg;ir. ap powerset_inc. ap Z_sub. cp (map_of_trans H5).
fold cs in H4. fold ct in H6.

pose (z := fun a => complement s (Im (ev g) (complement t (Im (ev f) a)))).
assert (Application.axioms (powerset s) (powerset s) z).
uf z;uhg;ir. ap powerset_inc. ap Z_sub.
assert (forall a b, sub a b -> sub (z a) (z b)).
ir. uf z. ap sub_complement.
ap Im_sub. ap sub_complement. ap Im_sub. am.

pose (F := Z (powerset s) (fun x => sub x (z x))).
assert (nonempty F). exists emptyset. ap Z_inc.
ap powerset_inc. ap emptyset_sub_all. ap emptyset_sub_all.

pose (G := union F).
assert (sub G s). uhg;ir. union_nin H10.
apply Z_sub in H10. apply powerset_sub in H10. au.
assert (forall x, inc x F -> sub x G).
ir. uhg;ir;ap union_inc. exists x;ee;au.
assert (forall x, inc x F -> sub x (z G)).
ir. cp (Z_all H12). ee. apply powerset_sub in H13.
apply sub_trans with (z x). am.
ap H8. ap H11. am.

assert (sub G (z G)). uhg;ir.
union_nin H13. eapply H12. am. am.
assert (sub (z G) (z (z G))). ap H8;am.
assert (inc (z G) F). ap Z_inc.
ap powerset_inc. ap Z_sub. am.
assert (sub (z G) G).
uhg;ir;ap union_inc. exists (z G). ee. am. am.

assert (z G = G). ap extensionality. am. am.
assert (complement s G = Im (ev g) (complement t (Im (ev f) G))).
transitivity (complement s (z G)). rw H17. tv.
uf z. ap complement_complement_id.
uhg;ir. Im_nin H18.
subst. ap H2. eapply Z_sub;am.

pose (h := fun x => by_cases 
(fun _ : inc x G => ev f x)
(fun _ : ~inc x G => ev (inverse g) x)).

assert (sub (complement s G) (range g)).
rw H18. uhg;ir.
Im_nin H19;subst. ap range_ev_inc. am.
replace (domain g) with t. eapply Z_sub;am. symmetry.
uh H0;ee;ap H0.

assert (Application.axioms s t h).
uhg;ir.
uf h.
apply by_cases with (inc x G);ir.
rw by_cases_if;try am.
ap H1. am.
rw by_cases_if_not;try am.
assert (inc x (complement s G)). ap Z_inc;am.
cp (H19 x H22).
apply inverse_ev_pr in H23;try am.
ee.
replace t with (domain g). am. uh H0;ee;ap H0.

assert (Hb : bijective t (range g) g).
uhg;ee.
uhg;ee. am. uh H0;ee;ap H0. ap sub_refl. am.
uhg;ir. apply range_ex in H21. nin H21;ee;subst.
exists x;ee;au. replace t with (domain g). am. uh H0;ee;ap H0.
am.

assert (bijective (range g) t (inverse g)).
ap bijective_inverse_bijective. am. 

assert (Application.bijective s t h).
uhg;ee. am.
uhg;ir. ufi h H24. apply by_cases with (inc x G);ir;apply by_cases with (inc y G);ir.
rwi by_cases_if H24;try am. rwi by_cases_if H24;try am.
ap H. am. am. am.

rwi by_cases_if H24;try am. rwi by_cases_if_not H24;try am.
assert (inc y (complement s G)).
ap Z_inc;am. rwi H18 H27. Im_nin H27;subst.
apply Z_all in H27;ee.
nin H28. ap Im_show_inc. exists x;ee.
am. rw H24. 
rw (bijective_inverse_ev_l Hb). tv. am.
rwi by_cases_if_not H24;try am. rwi by_cases_if H24;try am.
assert (inc x (complement s G)). ap Z_inc;au.
rwi H18 H27. Im_nin H27;subst.
apply Z_all in H27;ee. nin H28.
ap Im_show_inc. exists y;ee. am. wr H24. rw (bijective_inverse_ev_l Hb).
tv. am.

rwi by_cases_if_not H24;try am. rwi by_cases_if_not H24;try am.
ap H21. ap H19. ap Z_inc;au. ap H19. ap Z_inc;au.
am.
uhg;ir.
apply by_cases with (inc y (Im (ev f) G));ir.
Im_nin H23;subst.
exists x;ee. au. uf h. rw by_cases_if. tv. am.
cp H22. apply H21 in H24. nin H24;ee;subst.
exists x;ee. ap H0. am.
uf h. rw by_cases_if_not. tv.
uhg;ir.
wri H17 H25. apply Z_all in H25;ee.
ap H26. ap Im_show_inc. exists (ev (inverse g) x);ee.
ap Z_inc;am. symmetry. eapply bijective_inverse_ev_r. ap Hb.
am.

exists (L s h). ap map_of_bijective. am.
Qed.

End Map.

Module Equipotent.
Export Function. Export Map.

Lemma equipotent_union_strict : forall x y, 
(forall a b, inc a x -> inc b x -> nonempty (inter2 a b) -> a=b) -> 
(forall a b, inc a y -> inc b y -> nonempty (inter2 a b) -> a=b) ->
(exists f, bijective x y f & forall a, inc a x -> are_equipotent a (ev f a)) -> 
are_equipotent (union x) (union y).
Proof.
ir. destruct H1 as [f H1];ee.
cp (bijective_inverse_bijective H1).
assert (forall a, inc a y -> are_equipotent a (ev (inverse f) a)).
ir. cp (bijective_inverse_ev_r H1).
cp H4;apply H5 in H6. wr H6.
rw (bijective_inverse_ev_l H1). Focus 2. eapply trans_of_map;am.
ap are_equipotent_sym. ap H2. eapply trans_of_map;am.

rw are_equipotent_transformation.
pose (chpr := fun z a => inc a x & inc z a).
assert (Hch : forall z, inc z (union x) -> chpr z (unique_choose (chpr z))).
ir;ap unique_choose_pr.
union_nin H5. exists x0;uhg;ee;am.
uhg;ir. uh H6;ee;uh H7;ee.
ap H. am. am.
exists z. ap inter2_inc;am.

pose (chpr' := fun z b => inc b y & inc z b).
assert (Hch' : forall z, inc z (union y) -> chpr' z (unique_choose (chpr' z))).
ir;ap unique_choose_pr.
union_nin H5. exists x0;uhg;ee;am.
uhg;ir. uh H6;ee;uh H7;ee.
ap H0. am. am.
exists z. ap inter2_inc;am.

(*NEED CHOICE FOR THIS*)
assert (exists g, forall a, inc a x -> bijective a (ev f a) (g a)).
econstructor;ir. cp (choose_pr (H2 a H5)). simpl in H6.
ap H6.
destruct H5 as [g H5].
exists (fun z => let a := unique_choose (chpr z) in 
(*a is in x with z in a*)
ev (g a) z).
uhg;ee;uhg;ir.
cp (Hch x0 H6).
uh H7;ee.
ap union_inc.
cp (H5 (unique_choose (chpr x0)) H7).
cp H8;apply (bijective_of_map H9) in H8.
econstructor;ee. eapply trans_of_map. ap H1. ap H7.
am.

apply Hch in H6;apply Hch in H7.
set (a := unique_choose (chpr x0)) in *.
set (b := unique_choose (chpr y0)) in *.
uh H6;ee;uh H7;ee.
cp (H5 a H6);cp (H5 b H7).
cp H9. apply (bijective_of_map H11) in H13.
cp H10. apply (bijective_of_map H12) in H14.
assert (ev f a = ev f b).
ap H0. ap (bijective_of_map H1). am. ap (bijective_of_map H1). am.
exists (ev (g a) x0). ap inter2_inc. am. rw H8. am.

apply H1 in H15.
rwi H15 H8. apply H12.
wr H15. am. am. am. am. am.

union_nin H6.
cp H6. apply (bijective_of_map H1) in H8. nin H8;ee.
subst.
cp (H5 x1 H8).
cp H7. apply (bijective_of_map H9) in H10.
nin H10;ee. subst.
exists x0;dj. ap union_inc. exists x1;ee;am.

apply Hch in H11.
uh H11;ee.
assert (unique_choose (chpr x0) = x1).
ap H. am. am.
exists x0;ap inter2_inc;am.
rw H13. tv.
Qed.

Lemma union2_equipotent : forall a b, inter2 a b = emptyset -> 
forall a' b', inter2 a' b' = emptyset -> 
are_equipotent a a' -> are_equipotent b b' -> 
are_equipotent (union2 a b) (union2 a' b').
Proof.
ir;uf union2.
apply by_cases with (a = emptyset).
intros.
subst.
assert (a' = emptyset). ap empty_emptyset;ir.
nin H1;apply H1 in H3. nin H3;ee;edestruct emptyset_empty;am.
subst.
assert (union2 emptyset b = b).
ap extensionality. uhg;ir. apply union2_or in H3. nin H3.
edestruct emptyset_empty;am. am.
uhg;ir;ap union2_r;am. ufi union2 H3. rw H3.
assert (union2 emptyset b' = b').
ap extensionality. uhg;ir. apply union2_or in H4. nin H4.
edestruct emptyset_empty;am. am.
uhg;ir;ap union2_r;am. ufi union2 H4. rw H4. am.

intros Hnea.
apply by_cases with (b=emptyset).
ir. subst. assert (b' = emptyset).
ap empty_emptyset;ir.
nin H2;apply H2 in H3. nin H3;ee;edestruct emptyset_empty;am.
subst.
assert (union2 a emptyset = a).
ap extensionality. uhg;ir. apply union2_or in H3. nin H3. am.
edestruct emptyset_empty;am.
uhg;ir;ap union2_l;am. ufi union2 H3. rw H3.
assert (union2 a' emptyset = a').
ap extensionality. uhg;ir. apply union2_or in H4. nin H4. am.
edestruct emptyset_empty;am.
uhg;ir;ap union2_l;am. ufi union2 H4. rw H4. am.
intros Hneb.

assert (Hneq : a<>b).
uhg;ir;subst.
ap Hneb. ap empty_emptyset;ir.
destruct emptyset_empty with y. wr H;ap inter2_inc;am.
assert (Hneq' : a' <> b').
uhg;ir;subst.
ap Hnea. ap empty_emptyset;ir.
nin H1. apply (bijective_of_map H1) in H3.
edestruct emptyset_empty. wr H0. ap inter2_inc;am.



ap equipotent_union_strict.
ir. apply doubleton_or in H3;apply doubleton_or in H4.
nin H3;nin H4;subst;au.
rwi H H5. nin H5. edestruct emptyset_empty;am.
rwi inter2_comm H5. rwi H H5. nin H5. edestruct emptyset_empty;am.
ir. apply doubleton_or in H3;apply doubleton_or in H4.
nin H3;nin H4;subst;au.
rwi H0 H5. nin H5. edestruct emptyset_empty;am.
rwi inter2_comm H5. rwi H0 H5. nin H5. edestruct emptyset_empty;am.
exists (L (doubleton a b) (fun x => if eq_dec a x then a' else b')).
ee. ap map_of_bijective. uhg;ee;uhg;ir.
nin (eq_dec a x). ap doubleton_l. ap doubleton_r.
apply doubleton_or in H3;apply doubleton_or in H4;nin H3;nin H4;subst;au.
rwi eq_dec_if H5. rwi eq_dec_if_not H5. 
nin Hneq';am.
am. rwi eq_dec_if_not H5;au. rwi eq_dec_if H5. nin Hneq';au.
apply doubleton_or in H3;nin H3;subst.
exists a;ee. ap doubleton_l. rw eq_dec_if;au.
exists b;ee. ap doubleton_r. rw eq_dec_if_not;au.

ir. rw create_ev;au.
apply doubleton_or in H3;nin H3;subst. rw eq_dec_if;au. rw eq_dec_if_not;au.
Qed.

Lemma product_equipotent : forall a b a' b', are_equipotent a a' ->
 are_equipotent b b' -> are_equipotent (product a b) (product a' b').
Proof.
ir. rwi are_equipotent_transformation H;rwi are_equipotent_transformation H0.
rw are_equipotent_transformation.
nin H;nin H0.
exists (fun p => J (x (P p)) (x0 (Q p))).
uhg;ee;uhg;ir.
apply product_pr in H1;ee;nin H1. clpri H2;clpri H3;clpr.
ap product_pair_inc. ap H. am. ap H0;am.
apply product_pr in H1;apply product_pr in H2;ee;nin H1;nin H2.
clpri H4;clpri H5;clpri H6;clpri H7;clpri H3.
apply pair_eq in H3;ee. apply H in H1;au. apply H0 in H2;au.
subst;au.
apply product_pr in H1;ee;nin H1. clpri H2;clpri H3.
apply H in H2;apply H0 in H3.
nin H2;nin H3;ee;subst.
econstructor;ee. ap product_pair_inc;am.
clpr. tv.
Qed.

Lemma product_equipotent_assoc : forall a b c,
 are_equipotent (product a (product b c)) (product (product a b) c).
Proof.
ir.
uhg. exists (L ((product a (product b c))) (fun p => J (J (P p) (P (Q p))) (Q (Q p)))).
apply are_inverse_bijective with (L (product (product a b) c)
      (fun p => J (P (P p)) (J (Q (P p)) (Q ( p))))).
uhg;ee;ir;try (ap map_of_trans;uhg;ir).
apply product_pr in H;ee;nin H. clpri H0;clpri H1.
apply product_pr in H1;ee;nin H. clpri H1;clpri H2.
clpr. repeat ap product_pair_inc;am.
apply product_pr in H;ee;nin H. clpri H0;clpri H1.
apply product_pr in H0;ee;nin H. clpri H0;clpri H2.
clpr. repeat ap product_pair_inc;am.

uhg;ee;ir.
rw create_ev;au.
apply product_pr in H;ee;nin H. clpri H0;clpri H1.
apply product_pr in H1;ee;nin H. clpri H1;clpri H2.
clpr.
rw create_ev;au.
clpr. tv.
repeat ap product_pair_inc;am.
rw create_ev. apply product_pr in H.
ee. apply product_pr in H1;ee.
nin H. clpri H0;clpri H1. nin H1.
clpri H2;clpri H3. clpr.
repeat ap product_pair_inc;am.
am.
apply product_pr in H;ee. apply product_pr in H0;ee.
nin H. clpri H0. nin H0. clpri H2;clpri H1;clpri H3.
rw create_ev. rw create_ev.
clpr. tv.
repeat ap product_pair_inc;au.
rw create_ev. clpr. repeat ap product_pair_inc;au.
repeat ap product_pair_inc;au.
Qed.

Lemma injects_equipotent_Im : forall a f, Application.injects a f -> 
forall x, sub x a -> are_equipotent x (Im f x).
Proof.
ir.
uh H.
ap trans_equipotent.
exists f.
uhg;ee. uhg;ir. ap Im_inc;am.
uhg;ir. ap H;au.
uhg;ir.
Im_nin H1. exists x0;ee;au.
Qed.

End Equipotent.

Module Bounded.

(* a property is bounded P iff there is a set x = { y | P y } *)

Definition property (p : EP) (x : E) :=
  forall y : E, ((p y -> inc y x) & (inc y x -> p y)). 

Definition axioms (p : EP) := ex (property p).

Definition create (p : EP) := unique_choose (property p). 


Lemma criterion :
 forall p : EP,
 ex (fun x : E => forall y : E, p y -> inc y x) -> axioms p. 
ir. nin H. unfold axioms in |- *.
Proof.
eapply ex_intro with (Z x p). unfold property in |- *.
ir; xd; ir. 
ap Z_inc. ap H; au. au.
apply Z_pr in H0. am.
Qed. 



Lemma lem1 : forall (p : EP) (y : E), axioms p -> inc y (create p) -> p y.
Proof.
ir. unfold create in H0. unfold axioms in H. 
cp H.
apply unique_choose_pr in H1.
uh H1;ee.
destruct H1 with y;au.

uhg;ir.
uh H2;uh H3.
ap extensionality_rw;ir.
destruct H2 with a.
destruct H3 with a.
ap iff_eq;ir;au.
Qed. 

Lemma lem2 : forall (p : EP) (y : E), axioms p -> p y -> inc y (create p).
Proof.
ir.
uf create.
assert (property p (unique_choose (property p))).
ap unique_choose_pr.
am.
uhg;ir. ap extensionality_rw;ir.
destruct H1 with a;destruct H2 with a.
ap iff_eq;ir;au.
uh H1.
ap H1. am.
Qed.


Lemma inc_create :
 forall (p : EP) (y : E), axioms p -> inc y (create p) = p y. 
ir. 
ap iff_eq; ir. ap lem1; am. 
ap lem2; am. 
Qed. 

Lemma trans_criterion :
 forall (p : EP) (f : E1) (x : E),
 (forall y : E, p y -> ex (fun z : E => and (inc z x) (f z = y))) ->
 axioms p.
Proof.
ir. 
ap criterion. 
sh (Im f x). 
ir. ap Im_show_inc. apply H in H0. nin H0. exists x0;ee;au.
Qed. 

(*
Lemma blob : forall a (p : EP), (forall x, p x -> inc x a) ->
 (forall x y, p x -> p y -> x=y) -> 
forall x, p x -> 
union (Z a p) = x.
Proof.
ir.
ap extensionality;uhg;ir. apply union_ex in H2;nin H2;ee.
apply Z_all in H2;ee.
cp (H0 x x0 H1 H4). subst. am.
cp (H x H1).
ap union_inc. econstructor. ee. Focus 2. am. ap Z_inc.
am. am.
Qed.

Lemma blob' : forall a (p : EP), (forall x, p x -> inc x a) ->
 (forall x y, p x -> p y -> x=y) -> 
(ex p) -> union (Z a p) = choose p.
Proof.
ir. ap blob. am. am. ap choose_pr. am.
Qed.
*)

End Bounded.


Module Order.

Section Basics.

Variables (a : E) (r : E2P).
Hypothesis oH : is_order r a.

Notation lt := (lt_of r).

Variables x y z : E.
Hypotheses (Hx : inc x a) (Hy : inc y a) (Hz : inc z a).

Lemma lt_leq_trans : lt x y -> r y z -> lt x z.
Proof.
ir. uhg;ee. cp oH. uh H1;ee. apply H3 with y;am.
uhg;ir;subst. uh H;ee.
ap H1. ap oH;au.
Qed.

Lemma leq_lt_trans : r x y -> lt y z -> lt x z.
Proof.
ir. uhg;ee.
cp oH. uh H1;ee. apply H3 with y;am.
uhg;ir;subst.
ap H0. ap oH;au.
Qed.

Lemma leq_refl : r x x.
Proof.
ir. ap oH;am.
Qed.

Lemma leq_trans : r x y -> r y z -> r x z.
Proof.
ir;apply oH with y;am.
Qed. 

Lemma leq_antisym : r x y -> r y x -> x=y.
Proof.
ap oH;am.
Qed.

Lemma no_lt_leq : lt x y -> r y x -> False.
Proof.
ir. ap H. ap leq_antisym. am. am.
Qed. 

Lemma leq_eq_or_lt : r x y -> x = y \/ lt x y.
Proof.
ir. apply by_cases with (x=y);ir.
au. right;uhg;ee;am.
Qed.

End Basics.

Lemma subLt_sub_trans : forall x y, lt_of sub x y -> forall z, sub y z ->
 lt_of sub x z.
Proof.
ir;eapply lt_leq_trans.
Focus 2. ap union2_l. ap singleton_inc.
Focus 3. ap union2_r. ap union2_r. ap singleton_inc.
Focus 3. am.
Focus 2. ap union2_r. ap union2_l. ap singleton_inc.
ap sub_is_order. am.
Qed.

Lemma sub_subLt_trans : forall x y, sub x y -> forall z, lt_of sub y z ->
 lt_of sub x z.
Proof.
ir;uhg;ee. 
apply sub_trans with y;am.
uhg;ir;subst;ap H0;ap extensionality;am.
Qed.

Section Symmetric_order.

Variables (a : E) (r : E2P).
Hypothesis oH : is_order r a.

Definition symOrder x y := r y x.

Lemma symOrder_is_order : is_order symOrder a.
Proof.
cp oH. clear oH.
uh H;ee. uf symOrder.
uhg;ee;uhg;au.
ir. apply H1 with y;au.
Qed.

End Symmetric_order.

Lemma sym_sym_eq : forall r, symOrder (symOrder r) = r.
Proof.
ir. uf symOrder. ap arrow_extensionality. ir.
ap arrow_extensionality. ir. tv.
Qed.

Section Bounds.

Variable (a : E).

Definition is_upper_bound (r:E2P) b m := and (inc m a) (forall x, inc x b ->  r x m).

Definition is_lower_bound (r : E2P) b m := and (inc m a) (forall x, inc x b ->  r m x).

Definition upper_bounds r b := Z a (is_upper_bound r b).
Definition lower_bounds r b := Z a (is_lower_bound r b).

Lemma upper_bounds_inc : forall r b m, is_upper_bound r b m -> 
inc m (upper_bounds r b).
Proof.
ir;ap Z_inc;am.
Qed.

Lemma lower_bounds_inc : forall r b m, is_lower_bound r b m -> 
inc m (lower_bounds r b).
Proof.
ir;ap Z_inc;am.
Qed.

Definition is_super r b m := 
and (is_upper_bound r b m)
(forall x, is_upper_bound r b x -> r m x).

Definition is_inf r b m :=
and (is_lower_bound r b m)
(forall x, is_lower_bound r b x -> r x m).

Definition is_max r b m :=
and (is_upper_bound r b m)
(inc m b).

Definition is_min r b m :=
and (is_lower_bound r b m)
(inc m b).

Variable r:E2P.

Hypothesis oH : is_order r a.

Lemma super_upper : forall b m, is_super r b m -> is_upper_bound r b m.
Proof.
ir;am.
Qed.

Lemma inf_lower : forall b m, is_inf r b m -> is_lower_bound r b m.
Proof.
ir;am.
Qed.

Lemma max_upper : forall b m, is_max r b m -> is_upper_bound r b m.
Proof.
ir;am.
Qed.

Lemma min_lower : forall b m, is_min r b m -> is_lower_bound r b m.
Proof.
ir;am.
Qed.

Lemma super_unicity : forall b m, is_super r b m -> forall n, is_super r b n -> 
m=n.
Proof.
ir. ap oH;au.
ap H. ap super_upper;am.
ap H0. ap super_upper;am.
Qed.

Lemma inf_unicity : forall b, unicity (is_inf r b).
Proof.
uhg.
ir. ap oH;au.
ap H0. ap inf_lower;am.
ap H. ap inf_lower;am.
Qed.

Lemma max_super : forall b m, is_max r b m -> is_super r b m.
Proof.
ir. uh H;ee. uhg;ee;au.
ir.
uh H. ee.
uh H1;ee. ap H3. am.
Qed.

Lemma min_inf : forall b m, is_min r b m -> is_inf r b m.
Proof.
ir. uhg;ee. am.
ir. uh H;uh H0. ee.
ap H1. am.
Qed.

Lemma max_unicity : forall b, unicity (is_max r b).
Proof.
uhg;ir. apply super_unicity with b;au;ap max_super;au.
Qed.

Lemma min_unicity : forall b, unicity (is_min r b).
Proof.
uhg;ir. apply inf_unicity with b;au;ap min_inf;au.
Qed.

Definition chooseSuper b := unique_choose (is_super r b).
Definition chooseInf b := unique_choose (is_inf r b).

Lemma lower_symOrder : forall b m, is_lower_bound r b m =
 is_upper_bound (symOrder r) b m.
Proof.
ir. ap iff_eq;uhg;ee;au.
Qed.

Lemma inf_symOrder : forall b m, is_inf r b m = is_super (symOrder r) b m.
Proof.
ir. ap iff_eq;uhg;ee;au.
Qed.

Lemma min_symOrder : forall b m, is_min r b m = is_max (symOrder r) b m.
Proof.
uf symOrder. ir.
ap iff_eq;uhg;ee;au.
Qed.

Lemma chooseSup_pr : forall b, ex (is_super r b) -> is_super r b (chooseSuper b).
Proof.
ir. uf chooseSuper. ap unique_choose_pr.
am.
uhg;ir. eapply super_unicity.
am. am.
Qed.

Lemma chooseInf_pr : forall b, ex (is_inf r b) -> is_inf r b (chooseInf b).
Proof.
ir. uf chooseInf. ap unique_choose_pr.
am.
uhg;ir. eapply inf_unicity.
am. am.
Qed.

Lemma chooseSup_max : forall b, ex (is_max r b) -> is_max r b (chooseSuper b).
Proof.
ir.
nin H.
cp (max_super H).
cp (ex_intro (is_super r b) x H0). apply chooseSup_pr in H1.
cp (super_unicity H0 H1). subst. am.
Qed.

Lemma chooseInf_min : forall b, ex (is_min r b) -> is_min r b (chooseInf b).
Proof.
ir.
nin H.
cp (min_inf H).
cp (ex_intro (is_inf r b) x H0). apply chooseInf_pr in H1.
cp (inf_unicity H0 H1). subst. am.
Qed.

End Bounds.

Lemma super_min_bounds : forall a r b, is_super a r b =
 is_min a r (upper_bounds a r b).
Proof.
ir;ap arrow_extensionality;intros m.
ap iff_eq;ir.
uhg;ee. uhg;ee.
am. ir. apply Z_pr in H0. ap H. am.
ap upper_bounds_inc. am.
uhg;ee. eapply Z_pr. am.
ir. ap H. ap upper_bounds_inc. am.
Qed.

Lemma inf_max_bounds : forall a r b, is_inf a r b =
 is_max a r (lower_bounds a r b).
Proof.
ir;ap arrow_extensionality;intros m.
ap iff_eq;ir.
uhg;ee. uhg;ee.
am. ir. apply Z_pr in H0. ap H. am.
ap lower_bounds_inc. am.
uhg;ee. eapply Z_pr. am.
ir. ap H. ap lower_bounds_inc. am.
Qed.

Section Total.

Variables (a : E) (le : E2P).
Hypothesis toH : is_total_order le a.

Notation lt := (lt_of le).

Lemma lt_not_leq : forall x, inc x a -> forall y, inc y a -> 
lt x y = ~ le y x.
Proof.
ir. ap iff_eq;ir.
uhg;ir.
ap H1. ap toH. am. am. am. am.
uhg;ee. cp toH.
uh H2;ee. destruct H3 with x y;au.
destruct H1;au.
uhg;ir;subst. ap H1. ap toH. am.
Qed.

Lemma leq_not_lt : forall x, inc x a -> forall y, inc y a -> 
le x y = ~ lt y x.
Proof.
ir. rw lt_not_leq;try am.
ap iff_eq. ir;uhg;ir;au.
ap excluded_middle.
Qed.

End Total.

Section Well_order.

Definition is_well_order r a :=
 and (is_order r a) (forall b, sub b a -> nonempty b -> ex (is_min a r b)).

Lemma well_order_total : forall r a, is_well_order r a -> is_total r a.
Proof.
ir. uhg;ir.
uh H;ee.
destruct H2 with (doubleton x y).
uhg;ir. apply doubleton_or in H3. nin H3;rw H3;am.
exists x;ap doubleton_l.
uh H3;ee.
apply doubleton_or in H4. uh H3. ee.
nin H4;subst.
left. ap H5. ap doubleton_r.
right;ap H5;ap doubleton_l.
Qed.

Lemma well_order_total_order : forall r a, is_well_order r a -> is_total_order r a.
Proof.
ir;uhg;ee. am. ap well_order_total. am.
Qed.

Lemma wo_ind : 
 forall (r : E2P) (a : E) (H : is_well_order r a) (p : EP),
 (forall x : E,
  inc x a -> (forall y : E, inc y a -> lt_of r y x -> p y) -> p x) ->
 forall x : E, inc x (a) -> p x.
Proof.
intros r a H p H0.
ap excluded_middle;uhg;ir.
pose (np := Z a (fun x => ~ p x)).
uh H;ee.
destruct H2 with np.
ap Z_sub.
ap excluded_middle;uhg;ir.
ap H1. ir. ap excluded_middle;uhg;ir;ap H3;exists x;ap Z_inc;au.

uh H3;ee.
apply Z_all in H4;ee.
uh H3;ee.

ap H5.
ap H0. am. ir.
uh H8;ee.
ap excluded_middle;uhg;ir.
ap H9. ap H. am. am. am.
ap H6. ap Z_inc. am.
am.
Qed.

End Well_order.

Section Strict_order.

Lemma strict_of_order : forall r a, is_order r a -> is_strict_order (lt_of r) a.
Proof.
ir. uh H;ee;uhg;ee.
uhg;ir. uhg;ir;uh H3;ee;au.

uhg;ee. ir.
eapply lt_leq_trans. uhg;ee;am. am. ap H3. am. am. am.
Qed.

Definition leq_of (r:E2P) x y := (r x y) \/ (x=y).

Lemma order_of_strict : forall r a, is_strict_order r a -> is_order (leq_of r) a.
Proof.
ir. uh H;ee;uhg;ee.
uhg;ir. uhg;au.
uhg;ir.
uh H3;uh H4;ee.
nin H3.
nin H4.
ap False_rect. eapply H. am.
eapply H0. am. ap H1. am. am. am. au. au.

uhg;ir.
uh H3;uh H5;nin H3;nin H5;subst.
uhg. left. apply H0 with y;am.
left. am.
left. am.
right;tv.
Qed.

End Strict_order.

Section Suborder.

Variable (r : E2P) (a : E).

Lemma subreflexiveT : reflexiveT r a -> forall b, sub b a -> reflexiveT r b.
Proof.
ir. uhg;ir. au.
Qed.

Lemma subantisym : antisymmetricT r a -> forall b, sub b a -> antisymmetricT r b.
Proof.
uhg;ir;au.
Qed.

Lemma subsymmetricT : symmetricT r a -> forall b, sub b a -> symmetricT r b.
Proof.
uhg;ir;au.
Qed.

Lemma subtransitiveT : transitiveT r a -> forall b, sub b a -> transitiveT r b.
Proof.
uhg;ir;eauto.
Qed.

Lemma subirreflexiveT : irreflexiveT r a -> forall b, sub b a -> irreflexiveT r b.
Proof.
uhg;ir;au.
Qed.

Lemma suborder : is_order r a -> forall b, sub b a -> is_order r b.
Proof.
uhg;ir;ee;[eapply subreflexiveT | eapply subantisym | eapply subtransitiveT]; am.
Qed.

Lemma sub_strict_order : is_strict_order r a -> forall b, sub b a ->
 is_strict_order r b.
Proof.
uhg;ir;ee;[eapply subirreflexiveT | eapply subtransitiveT];am.
Qed.

Lemma sub_total : is_total r a -> forall b, sub b a -> is_total r b.
Proof.
uhg;ir;au.
Qed.

Lemma sub_totalorder : is_total_order r a -> forall b, sub b a ->
 is_total_order r b.
Proof.
uhg;ir;ee;[eapply suborder | eapply sub_total];am.
Qed.

Lemma subequivalence : is_equivalence r a -> forall b, sub b a ->
 is_equivalence r b.
Proof.
uhg;ir;ee;[eapply subreflexiveT | eapply subsymmetricT | eapply subtransitiveT ] ;am.
Qed.

Lemma sub_upper_bound : forall b, sub b a ->
 forall x y, is_upper_bound b r x y -> is_upper_bound a r x y.
Proof.
ir. uhg;ee. ap H;am. ap H0.
Qed.

Lemma sub_lower_bound : forall b, sub b a ->
 forall x y, is_lower_bound b r x y -> 
is_lower_bound a r x y.
Proof.
ir;uhg;ee;au. ap H;am.
Qed.

Lemma sub_min : forall b, sub b a ->
 forall x, sub x b -> is_min b r x = is_min a r x.
Proof.
ir;repeat (ap arrow_extensionality;ir).
ap iff_eq;ir. uhg;ee. eapply sub_lower_bound. am. am.
am.
uhg;ee.
uhg;ee. ap H0;am. am. am.
Qed.

Lemma sub_max : forall b, sub b a ->
 forall x, sub x b -> is_max b r x = is_max a r x.
Proof.
ir;repeat (ap arrow_extensionality;ir).
ap iff_eq;ir. uhg;ee. eapply sub_upper_bound. am. am.
am.
uhg;ee.
uhg;ee. ap H0;am. am. am.
Qed.

(*note : sub_inf doesn't work because eg is_inf [0 ; 1] rLeq  [-6 ; -5] 0
but not is_inf R rLeq [-6 ; -5] 0*)

Lemma sub_wellorder : is_well_order r a ->
 forall b, sub b a -> is_well_order r b.
Proof.
uhg;ir;ee. eapply suborder;am.
ir.
rw (sub_min H0). ap H;try am. eapply sub_trans;am. am.
Qed.

End Suborder.

Section Initial.

Definition is_initial_segment r a b := 
and (sub b a)
(forall x y, inc x a -> inc y b -> r x y -> inc x b).

Definition initial_segment_of r a (b:E) := Z a (fun x => lt_of r x b).

Lemma initial_of_initial : forall r a, is_order r a -> forall b, inc b a ->
 is_initial_segment r a (initial_segment_of r a b).
Proof.
ir;uhg;ee;ir. ap Z_sub.
apply Z_all in H2;ee;ap Z_inc. am.
uhg;ee. eapply H. am. ap H2. am. am. am.
uhg;ir;subst. ap H4. ap H;au. 
Qed.

Lemma well_order_initial : forall r a, is_well_order r a -> forall b, 
is_initial_segment r a b ->
 (exists b', inc b' a & b = initial_segment_of r a b') \/ (b=a).
Proof.
ir. apply by_cases with (nonempty (complement a b));ir.
apply H in H1. nin H1. left. exists x. ee. am.
ap extensionality;uhg;ir.
ap Z_inc. ap H0. am. uh H0;ee.
assert (is_total r a). ap well_order_total. am.
destruct H4 with a0 x. ap H0;am. am.
uhg;ee. am.
uhg;ir. subst. 
uh H1;ee. apply Z_pr in H6;nin H6;am.

uh H1;ee. apply Z_pr in H6;nin H6.
apply H3 with a0. am. am. am.

apply Z_all in H2. ee.
eapply use_complement. am.
uhg;ir.
cp H4. apply H1 in H5.
ap H3. ap H;au.
ap Z_sub.

right. ap extensionality;try am;uhg;ir.
ap excluded_middle;uhg;ir;ap H1;exists a0;ap Z_inc;am.
Qed.


End Initial.

End Order.

Module Relation_Morphism.
Import Order. Import Function.
Import Map.

Section Definitions.

Variables (r : E2P) (a : E) (r' : E2P) (b : E).

Definition is_morphism f := and (is_map a b f) 
(forall x, inc x a -> forall y, inc y a -> r x y -> r' (ev f x) (ev f y)).

End Definitions.

Section Total_Order_Morphism.

Lemma total_injective_leq_back : forall a r, is_total_order r a ->  
 forall a' r', is_order r' a' -> 
 forall f, is_morphism r a r' a' f -> 
 Application.injects a (ev f) ->
 forall x y, inc x a -> inc y a -> 
 r' (ev f x) (ev f y) -> r x y.
Proof.
ir.

rw (leq_not_lt H);au.
uhg;ir.
uh H6;ee. uh H1;ee.
cp (H8 y H4 x H3 H6).
ap H7. ap H2;au.
ap H0;apply trans_of_map in H1;au.
Qed. 

Lemma total_injective_lt_back : forall a r, is_total_order r a ->  
 forall a' r', is_order r' a' -> 
 forall f, is_morphism r a r' a' f -> 
 Application.injects a (ev f) ->
 forall x y, inc x a -> inc y a -> 
 lt_of r' (ev f x) (ev f y) -> lt_of r x y.
Proof.
ir.
uhg;ee.
eapply total_injective_leq_back. am. ap H0.
am. am. am. am. am.
uhg;ir;ap H5. rw H6;tv.
Qed.

End Total_Order_Morphism.

Definition is_isomorphism (r : E2P) (a : E) (r' : E2P) (b : E) f :=
 and (is_morphism r a r' b f) (bijective a b f).

Lemma isomorphism_rw : forall r a r' b f, is_isomorphism r a r' b f =
 and (is_morphism r a r' b f)
 (and (Application.injects a (ev f))
 (Application.covers a b (ev f))).
Proof.
ir;ap iff_eq;ir;ee;au.
uhg;ee. am. uhg;ee;am.
Qed.

Definition are_rel_isomorphic r a r' b := ex (is_isomorphism r a r' b).

Lemma are_rel_iso_refl : forall r a, are_rel_isomorphic r a r a.
Proof.
ir. exists (id a). uhg;ee. uhg;ee.
ap id_map. ir. rw id_ev. rw id_ev. am. am. am.
ap id_bijective.
Qed.

Lemma morphism_compose : forall r a r' a' r'' a'' f g, is_morphism r a r' a' f -> 
is_morphism r' a' r'' a'' g -> is_morphism r a r'' a'' (compose g f).
Proof.
ir. uhg;ee.
apply map_compose with a';am.
ir. uh H;ee;uh H0;ee. cp (trans_of_map H);cp (trans_of_map H0).
rw compose_ev;au. rw compose_ev;au.
rw composable_domain. uh H;ee. rw H8;am.
eapply map_composable. am. am.
rw composable_domain. uh H;ee. rw H8;am.
eapply map_composable. am. am.
Qed.

Lemma isomorphism_compose : forall r a r' a' r'' a'' f g, is_isomorphism r a r' a' f -> 
is_isomorphism r' a' r'' a'' g -> is_isomorphism r a r'' a'' (compose g f).
Proof.
ir. uhg;ee. eapply morphism_compose;am.
eapply bijective_compose;am.
Qed.

Lemma are_rel_iso_trans : forall r a r' a' r'' a'', are_rel_isomorphic r a r' a' -> 
are_rel_isomorphic r' a' r'' a'' -> are_rel_isomorphic r a r'' a''.
Proof.
ir. nin H;nin H0.
exists (compose x0 x).
eapply isomorphism_compose;am.
Qed.

Lemma isomorphism_inverse : forall r a r' a' f (Ht : is_total_order r a)
(Ho : is_order r' a'), is_isomorphism r a r' a' f -> 
is_isomorphism r' a' r a (inverse f).
Proof.
ir. uhg;ee.
uhg;ee. apply bijective_inverse_bijective. am.
ir.
assert (are_inverse a a' f (inverse f)). ap bijective_inverse_of. am.
uh H3;ee. uh H5;ee.
eapply (total_injective_leq_back Ht Ho).
am. am. eapply trans_of_map;try am. eapply trans_of_map;try am.
repeat rw H6;am.
ap bijective_inverse_bijective. am.
Qed.

Lemma are_rel_iso_sym : forall r a r' a' (Ht : is_total_order r a)
(Ho : is_order r' a'), are_rel_isomorphic r a r' a' -> 
are_rel_isomorphic r' a' r a.
Proof.
ir. nin H. exists (inverse x). ap isomorphism_inverse;am.
Qed.

Lemma isomorphism_of_trans : forall (r:E2P) a (r':E2P) a' f,
 Application.bijective a a' f -> 
(forall x y, inc x a -> inc y a -> r x y -> r' (f x) (f y)) ->
 is_isomorphism r a r' a' (create a f).
Proof.
ir. uhg;ee.
uhg;ee. ap map_of_trans;am.
ir. rw create_ev;au. rw create_ev;au.
ap map_of_bijective. am.
Qed.

End Relation_Morphism. Export Relation_Morphism.

