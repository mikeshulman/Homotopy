(** Coherentification/adjointification of homotopy equivalences. *)

Require Import Homotopy.
Require Import MoreDefinitions.

(** For compatibility with Coq 8.2 we unset automatic parameter introduction. *)

Unset Automatic Introduction.

(** We have proven that every equivalence has an inverse up to
homotopy.  In fact, having an inverse up to homotopy is also enough to
characterize a map as being an equivalence.  However, the data of an
inverse up to homotopy is not equivalent to the data in [is_equiv]
unless we add one more piece of coherence data.  This is a homotopy
version of the category-theoretic notion of "adjoint equivalence". *)

Definition is_adjoint_equiv {A B} (f : A -> B) :=
  { g : B -> A
    & { is_section : forall y, (f (g y)) ~~> y
      & { is_retraction : forall x, (g (f x)) ~~> x
        & forall x, (map f (is_retraction x)) ~~> (is_section (f x))
          }}}.

Theorem equiv_to_adjoint {A B} (f: A -> B) : is_equiv f -> is_adjoint_equiv f.
  intros A B fmap E.
  set (f := existT _ fmap E : equiv A B).
  (* The following are the natural things to write, but with the
     definitions of these functions in Equivalence.v via tactics, I
     wasn't able to get the rest of the proof to work.
  set (g := equiv_inv f); exists g.
  set (is_section := equiv_inv_is_is_section f); exists is_section.
  set (is_retraction := equiv_inv_is_is_retraction f); exists is_retraction.
  *)
  set (g := fun y => projT1 (projT1 (E y))); exists g.
  set (is_section := fun y => projT2 (projT1 (E y))); exists is_section.
  set (is_retraction := fun x => ! map (@projT1 _ _) (projT2 (E (f x)) (existT _ x (idpath _)))); exists is_retraction.
  intro x.
  path_via (projT2 (projT1 (projT2 f (f x)))).
  path_via (map f (is_retraction x) @ idpath _).
  path_via ((!!map f (is_retraction x)) @ idpath _).
  apply concat_moveleft_onleft, opposite.
  path_via (map f (map (@projT1 _ _) (projT2 (projT2 f (f x)) (existT _ x (idpath _))))
    @ projT2 (projT1 (projT2 f (f x)))).
  path_via (map f (!is_retraction x)).
  unfold is_retraction, equiv_inv_is_retraction.
  apply opposite_opposite.
  exact (hfiber_triangle (projT2 (projT2 f (f x)) (existT _ x (idpath _)))).
Defined.

Theorem adjoint_to_equiv {A B} (f: A -> B) : is_adjoint_equiv f -> is_equiv f.
Proof.
  intros A B f E.
  destruct E as (g,(is_section,(is_retraction,tau))).
  intro y.
  contract_hfiber (g y) (is_section y).
  apply (total_paths _
    (fun x => f x ~~> y)
    (existT _ z q)
    (existT _ (g y) (is_section y))
    (!is_retraction z @ (map g q))).
  simpl.
  (** We want to apply [trans_is_concat], but first we need to apply [map_trans].  *)
  path_via (transport (P := fun y0 => y0 ~~> y)
    (map f (!is_retraction z @ map g q)) q).
  apply (map_trans (fun y0 => y0 ~~> y)).
  path_via (!map f (!is_retraction z @ map g q) @ q).
  apply trans_is_concat_opp.
  (** Now we rearrange things a bit. *)
  path_via (map f (!(!is_retraction z @ map g q)) @ q).
  path_via (map f (!map g q @ !!is_retraction z) @ q).
  path_via (map f (!map g q @ is_retraction z) @ q).
  path_via ((map f (!map g q) @ map f (is_retraction z)) @ q).
  (** Here is where we use tau, although it isn't obvious. *)
  path_via ((map f (!map g q) @ is_section (f z)) @ q).
  (** Next we apply naturality of 'is_section'. *)
  path_via (map f (!map g q) @ ((is_section (f z)) @ q)).
  apply concat_associativity.
  path_via (map f (!map g q) @ (is_section (f z) @ map (idmap B) q)).
  apply whisker_left, opposite, idmap_map.
  path_via (map f (!map g q) @ (map (f o g) q @ is_section y)).
  apply opposite, (homotopy_natural B B (f o g) (idmap B) is_section (f z) y q).
  (** And now it's straightforward. *)
  path_via (map f (!map g q) @ map (f o g) q @ is_section y).
  apply opposite, concat_associativity.
  path_via (idpath _ @ is_section y).
  path_via (map f (map g (!q)) @ map (f o g) q).
  path_via (map (f o g) (!q) @ map (f o g) q).
  path_via (map (f o g) (!q @ q)).
  apply opposite, concat_map.
  path_via (map (f o g) (idpath y)).
  apply map, opposite_left_inverse.
Defined.

(** Probably equiv_to_adjoint and adjoint_to_equiv are actually
inverse equivalences, at least if we assume function
extensionality. *)

(** Now, a central fact about adjoint equivalences is that any
"incoherent" equivalence can be improved to an adjoint equivalence by
changing one of the natural isomorphisms.  We now prove a
corresponding result in homotopy type theory. *)

Definition incoherent_equiv {A B} (f : A -> B) :=
  { g : B -> A &
    ( (forall y, f (g y) ~~> y)  *  (forall x, g (f x) ~~> x ))%type }.

(** The proof is long, but it is exactly the same as the usual proof
for adjoint equivalences in 2-category theory.
*)

Definition adjointify {A B} (f : A -> B)
  : incoherent_equiv f -> is_adjoint_equiv f.
Proof.
  intros A B f.
  unfold incoherent_equiv, is_adjoint_equiv.
  intro E.
  destruct E as (g,(is_section,is_retraction)).
  exists g. exists is_section.
  (** Not "exists is_retraction" !  We have to change one of them. *)
  exists (fun x =>
    ( map g (map f (!is_retraction x)))
    @ (map g (is_section (f x)))
    @ (is_retraction x)).
  intro x.
  (** Now we just play with naturality until things cancel. *)
  path_via (!! is_section (f x)).
  path_via ((!! is_section (f x)) @ idpath _).
  apply concat_moveright_onleft.
  path_via ((!is_section (f x)) @
   (map f (map g (map f (!is_retraction x)) @ map g (is_section (f x))) @
   map f (is_retraction x))).
  (* For some reason path_via can't handle this associativity. *)
  apply (concat (opposite (concat_associativity _ _ _ _ _ _ _ _))).
  path_via ((!is_section (f x) @
    ((map f (map g (map f (!is_retraction x)))) @
    (map f (map g (is_section (f x)))))) @
    map f (is_retraction x)).
  path_via (!is_section (f x) @
    map f (map g (map f (!is_retraction x))) @
    map f (map g (is_section (f x))) @
    map f (is_retraction x)).
  apply opposite, concat_associativity.
  path_via ((!is_section (f x) @ map (f o g) (map f (!is_retraction x)) @
    map f (map g (is_section (f x)))) @ map f (is_retraction x)).
  apply whisker_right, whisker_left, opposite, composition_map.
  path_via (map (idmap B) (map f (!is_retraction x)) @
    (!is_section (f (g (f x)))) @
    map f (map g (is_section (f x))) @
    map f (is_retraction x)).
  apply whisker_right, opposite.
  apply (homotopy_natural B B _ _
    (fun y => !is_section y)
    (f x) (f (g (f x)))
    (map f (!is_retraction x))).
  path_via (map f (!is_retraction x) @
    (!is_section (f (g (f x)))) @
    map f (map g (is_section (f x))) @
    map f (is_retraction x)).
  path_via (map f (!is_retraction x) @
    (!is_section (f (g (f x))) @
      map f (map g (is_section (f x)))) @
    map f (is_retraction x)).
  apply concat_associativity.
  path_via (map f (!is_retraction x) @
    (!is_section (f (g (f x))) @
      map (f o g) (is_section (f x))) @
    map f (is_retraction x)).
  apply whisker_left, whisker_left, opposite, composition_map.
  path_via (map f (!is_retraction x) @
    (map (idmap B) (is_section (f x)) @ (!is_section (f x))) @
    map f (is_retraction x)).
  apply whisker_left, opposite.
  apply (homotopy_natural B B _ _
    (fun y => !is_section y)
    (f (g (f x))) (f x)
    (is_section (f x))).
  path_via ((map f (!is_retraction x) @ (is_section (f x) @ !is_section (f x))) @
   map f (is_retraction x)).
  path_via ((map f (!is_retraction x) @ idpath _) @
   map f (is_retraction x)).
  path_via (map f (!is_retraction x) @ map f (is_retraction x)).
  path_via (map f (!is_retraction x @ is_retraction x)).
  path_via (map f (idpath x)).
Defined.

(** In Voevodsky's file the following corollary is called "gradth",
but only a couple of the people involved that night at CMU were grad
students at the time.  It can be phrased as "any homotopy equivalence
is an equivalence."  *)

Definition cmu_theorem {A B} (f : A -> B) (g : B -> A)
  (is_section : forall y, f (g y) ~~> y) (is_retraction : forall x, g (f x) ~~> x)
  : is_equiv f
  := adjoint_to_equiv f (adjointify f (existT _ g (pair is_section is_retraction))).

(** All sorts of nice things follow from this theorem.  For instance,
we can deduce the following lemma, proven more directly before. *)

Definition equiv_pointwise_idmap_ALT A (f : A -> A) (p : forall x, f x ~~> x)
  : is_equiv f
  := cmu_theorem f (idmap _) p p.

(** And the 2-out-of-3 property for equivalences. *)

Definition equiv_compose {A B C} (f : equiv A B) (g : equiv B C) : (equiv A C).
Proof.
  intros.
  exists (g o f).
  apply @cmu_theorem with
    (A := A) (B := C)
    (f := g o f)
    (g := (equiv_inv f) o (equiv_inv g) ).
  intro y.
  path_via (g ((f o (equiv_inv f)) (equiv_inv g y))).
  path_via (g (equiv_inv g y)).
  apply map.
  apply equiv_inv_is_section.
  apply equiv_inv_is_section.
  intro x.
  path_via (equiv_inv f (((equiv_inv g) o g) (f x))).
  path_via (equiv_inv f (f x)).
  apply map.
  apply equiv_inv_is_retraction.
  apply equiv_inv_is_retraction.
Defined.

Definition equiv_cancel_right {A B C} (f : equiv A B) (g : B -> C) :
  is_equiv (g o f) -> is_equiv g.
Proof.
  intros A B C f g H.
  set (gof := (existT _ (g o f) H) : equiv A C).
  apply @cmu_theorem with
    (A := B) (B := C)
    (f := g)
    (g := f o equiv_inv gof).
  intro y.
  path_via ((gof) (equiv_inv gof y)).
  apply equiv_inv_is_section.
  intro x.
  path_via (f (equiv_inv gof (g x))).
  path_via (f (equiv_inv f x)).
  path_via (f (equiv_inv gof (gof (equiv_inv f x)))).
  apply map. apply map.
  path_via (g (f (equiv_inv f x))).
  apply map. apply opposite. apply equiv_inv_is_section.
  apply map.
  apply equiv_inv_is_retraction.
  apply equiv_inv_is_section.
Defined.

Definition equiv_cancel_left {A B C} (f : A -> B) (g : equiv B C) :
  is_equiv (g o f) -> is_equiv f.
Proof.
  intros A B C f g H.
  set (gof := existT _ (g o f) H : equiv A C).
  apply @cmu_theorem with
    (A := A) (B := B)
    (f := f)
    (g := equiv_inv gof o g).
  intros y.
  path_via (equiv_inv g (g y)).
  path_via (equiv_inv g (g (f (equiv_inv gof (g y))))).
  apply opposite, equiv_inv_is_retraction.
  apply map.
  path_via (gof (equiv_inv gof (g y))).
  apply equiv_inv_is_section.
  apply equiv_inv_is_retraction.
  intros x.
  path_via (equiv_inv gof (gof x)).
  apply equiv_inv_is_retraction.
Defined.

(** André Joyal suggested the following definition of equivalences,
and to call it "h-isomorphism". *)

Definition is_hiso {A B} (f : A -> B) :=
  ( { g:B->A & forall x, g (f x) ~~> x} *
    { h:B->A & forall y, f (h y) ~~> y} )%type.

Theorem equiv_to_hiso {A B} (f : equiv A B) : is_hiso f.
Proof.
  intros A B f.
  split.
  exists (equiv_inv f).
  apply equiv_inv_is_retraction.
  exists (equiv_inv f).
  apply equiv_inv_is_section.
Defined.

Theorem hiso_to_equiv {A B} (f : A -> B) : is_hiso f -> is_equiv f.
Proof.
  intros A B f H.
  destruct H as ((g, is_retraction), (h, is_section)).
  apply @cmu_theorem with (A := A) (B := B) (f := f) (g := g).
  intro y.
  path_via (f (h y)).
  apply map.
  path_via (g (f (h (y)))).
  apply map, opposite, is_section.
  assumption.
Defined.

(** Of course, the harder part is showing that is_hiso is a proposition. *)
