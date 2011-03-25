(** Some more basic definitions of homotopy theory. *)

Require Import HomotopyDefinitions.

(** For compatibility with Coq 8.2 we unset automatic parameter introduction. *)

Unset Automatic Introduction.

(** Whiskering paths-between-paths by other paths. *)

Definition whisker_right A (x y z : A) (p p' : x ~~> y) (q : y ~~> z) :
  (p ~~> p') -> (p @ q ~~> p' @ q).
Proof.
  path_induction.
Defined.

Definition whisker_left A (x y z : A) (p : x ~~> y) (q q' : y ~~> z) :
  (q ~~> q') -> (p @ q ~~> p @ q').
Proof.
  path_induction.
Defined.

Hint Resolve whisker_right whisker_left : path_hints.

(** Paths between paths induce paths between their opposites. *)

Definition opposite2 A {x y : A} (p q : x ~~> y) (a : p ~~> q) : (!p ~~> !q).
Proof.
  path_induction.
Defined.

(* Mates *)

Lemma concat_moveleft_onright A (x y z : A) (p : x ~~> z) (q : x ~~> y) (r : y ~~> z) :
  (p ~~> q @ r) -> (p @ !r ~~> q).
Proof.
  intros A x y z p q r.
  intro a.
  apply concat_cancel_right with (r := r).
  path_via (p @ (!r @ r)).
  apply concat_associativity.
  path_via (p @ idpath z).
  path_via p.
Defined.

Lemma concat_moveright_onright A (x y z : A) (p : x ~~> y) (q : x ~~> z) (r : y ~~> z) :
  (p @ r ~~> q) -> (p ~~> q @ !r).
Proof.
  intros A x y z p q r.
  intro a.
  apply concat_cancel_right with (r := r).
  path_via (q @ (!r @ r)).
  path_via q.
  path_via (q @ idpath _).
  apply opposite, concat_associativity.
Defined.

Lemma concat_moveright_onleft A (x y z : A) (p : y ~~> z) (q : x ~~> z) (r : x ~~> y) :
  (r @ p ~~> q) -> (p ~~> !r @ q).
Proof.
  intros A x y z p q r.
  intro a.
  apply concat_cancel_left with (p := r).
  path_via ((r @ !r) @ q).
  path_via q.
  path_via (idpath _ @ q).
  apply concat_associativity.
Defined.

Lemma concat_moveleft_onleft A (x y z : A) (p : x ~~> z) (q : y ~~> z) (r : x ~~> y) :
  (p ~~> r @ q) -> (!r @ p ~~> q).
Proof.
  intros A x y z p q r.
  intro a.
  apply concat_cancel_left with (p := r).
  path_via ((r @ !r) @ p).
  apply opposite, concat_associativity.
  path_via p.
  path_via (idpath _ @ p).
Defined.

(** A version of [map] for dependent functions. *)

Lemma map_dep {A} {P : A -> Type} {x y : A} (f : forall x, P x)
  (p: x ~~> y) : (transport p (f x) ~~> f y).
Proof.
  path_induction.
Defined.

(** Similarly, [happly] for dependent functions. *)

Lemma happly_dep {A} {P : A -> Type} {f g : forall x, P x} : (f ~~> g) -> (forall x, f x ~~> g x).
Proof.
  path_induction.
Defined.

(** Transporting a path along another path is equivalent to
concatenating the two paths. *)

Lemma trans_is_concat {A} {x y z : A} (p : x ~~> y) (q : y ~~> z) :
  (transport q p) ~~> p @ q.
Proof.
  path_induction.
Defined.

Lemma trans_is_concat_opp {A} {x y z : A} (p : x ~~> y) (q : x ~~> z) :
  (transport (P := fun x' => (x' ~~> z)) p q) ~~> !p @ q.
Proof.
  path_induction.
Defined.

(** Transporting along a concatenation is transporting twice. *)

Lemma trans_concat {A} {P : A -> Type} {x y z : A} (p : x ~~> y) (q : y ~~> z) (z : P x) :
  transport (p @ q) z ~~> transport q (transport p z).
Proof.
  path_induction.
Defined.

(** Transporting commutes with pulling back along a map. *)

Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B)
 (p : x ~~> y) (z : P (f x))
  : (transport (P := (fun x => P (f x))) p z) ~~> (transport (map f p) z).
Proof.
  path_induction.
Defined.

(** If a space is contractible, then any two points in it are
connected by a path in a canonical way. *)

Lemma contr_path {A} (x y:A) : (contractible A) -> (x ~~> y).
Proof.
  intros A x y H.
  destruct H as (z,p).
  path_via z.
Defined.

(** Similarly, any two parallel paths in a contractible space are homotopic.  *)

Lemma contr_path2 {A} {x y:A}(p q:x ~~> y) : (contractible A) -> (p ~~> q).
Proof.
  intros X x y p q ctr.
  destruct ctr as (c, ret).
  path_via (ret x @ !ret y).
  apply concat_moveright_onright.
  path_via ((!!p) @ ret y).
  apply concat_moveleft_onleft.
  apply opposite.
  exact (! trans_is_concat_opp p (ret x)  @  map_dep ret p ).
  apply concat_moveleft_onright.
  path_via ((!!q) @ ret y).
  apply concat_moveright_onleft.
  exact (! trans_is_concat_opp q (ret x)  @  map_dep ret q).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)

Lemma contr_pathcontr {A} (x y : A) : contractible A -> contractible (x ~~> y).
Proof.
  intros A x y ctr.
  exists (contr_path x y ctr).
  intro p.
  apply contr_path2.
  assumption.
Defined.

(** The total space of any based path space is contractible. *)

Lemma pathspace_contr {X} (x:X) : contractible { y:X  &  x ~~> y }.
Proof.
  intros. unfold contractible.
  exists (existT (fun y => x ~~> y) x (idpath x)).
  intro z. destruct z as (y,p). path_induction.
Defined.

(** This lemma tells us how to extract a commutative triangle in the
base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x ~~> y) :
  (map f (map (@projT1 _ _) p)) @ (projT2 y) ~~> (projT2 x).
Proof.
  intros. induction p.
  path_via (idpath _ @ projT2 x).
Defined.
