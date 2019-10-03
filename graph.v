Set Implicit Arguments.
Unset Strict Implicit.

Require Export utils1.

Module Graph.

Inductive is_graph : EP :=
  | graph_is_graph : forall v e, relates e v v -> is_graph (pair v e).

Definition vertices := P. Definition edges := Q.

Lemma graph_relates : forall g, is_graph g -> relates (edges g) (vertices g) (vertices g).
Proof.
ir. nin H. uf edges;uf vertices. clpr. am.
Qed.

Inductive exists_path : E3P := 
  | path_edge : forall g x y, R (edges g) x y -> exists_path g x y
  | path_trans : forall g x y, R (edges g) x y -> forall z, exists_path g y z -> exists_path g x z
.

Inductive is_path : E4P := 
  | path_one : forall g x y, R (edges g) x y -> is_path g x y (econs x (econs y enil))
  | path_next : forall g x y, R (edges g) x y -> forall z p, is_path g y z p -> is_path g x z (econs x p)
.

Lemma exists_path_rw : forall g x y, exists_path g x y = ex (is_path g x y).
Proof.
ir;ap iff_eq. ir. nin H.
exists (econs x (econs y enil)). constructor. am.
nin IHexists_path. exists (econs x x0). 
eapply path_next. am. am.

ir. destruct H as [p H]. nin H.
ap path_edge. am.
eapply path_trans. am. am.
Qed.

Lemma path_list : forall g x y l, is_path g x y l -> is_elist l.
Proof.
ir;nin H.
lSolve. lSolve.
Qed.

Lemma path_ev_0 : forall g x y l, is_path g x y l -> ev l n0 = x.
Proof.
ir;nin H.
rw econs_0. tv. lSolve.
rw econs_0. tv. eapply path_list. am.
Qed.

