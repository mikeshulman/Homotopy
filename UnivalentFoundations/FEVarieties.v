(** Comparison of different varieties of function extensionality. *)

Require Import Homotopy.
Require Import MoreDefinitions.
Require Import AdjointEquivalence.

(** For compatibility with Coq 8.2 we unset automatic parameter introduction. *)

Unset Automatic Introduction.

(** (One can show that the inverse of [etaD] coming from its being an
equivalence is just the identity, and [etaD_axiom] is the unit and
counit of the adjoint equivalence.) *)

(** The simplest notion we call "naive functional extensionality".
This is what a type theorist would probably write down if (s)he were
thinking of types as sets and identity types as merely equalities: it
says that if two functions are equal pointwise, then they are equal.
It comes in both ordinary and dependent versions. *)

Definition naiveFE : Type := forall (X Y:Type) (f g: X -> Y)
  (p : forall x:X, (f x) ~~> (g x)), f ~~> g.

Definition naiveDFE : Type := forall (X:Type) (P: X -> Type)
  (f g: forall x:X, P x) (p : forall x:X, (f x) ~~> (g x)), f ~~> g.

(** This is sufficient for some purposes, such as the following. *)

Theorem contr_contr {X} : naiveDFE -> contractible X -> contractible (contractible X).
  intros X K ctr1.
  exists ctr1. intros ctr2.
  apply (total_paths _ _ ctr2 ctr1 (projT2 ctr1 (projT1 ctr2))).
  apply K. intro x.
  apply contr_path2. assumption.
Defined.


(** However, there are clearly going to be problems with this in the
homotopy world, since "being equal" is not merely a property, but
being equipped with a path is structure.  We should expect some sort
of coherence or canonicity of the path from f to g relating it to the
pointwise homotopy we started with.

A natural way to state a "homotopically good" notion of function
extensionality is to observe that there is a canonical map in the
other direction, taking paths between functions to pointwise
homotopies.  We can thus just ask for that map to be an equivalence.
We call this "strong functional extensionality."  Of course, it also
comes in ordinary and dependent versions.  *)

Definition FEmap {X Y:Type} (f g: X -> Y) (p : f ~~> g) : (forall x, (f x) ~~> (g x))
  := fun x => map (fun h => h x) p.

Definition DFEmap {X:Type} {P: X -> Type} (f g: forall x:X, P x) (p:f ~~> g) : (forall x:X, (f x) ~~> (g x))
  := fun x => map (fun h => h x) p.

Definition strongFE : Type :=
  forall (X Y:Type) (f g: X -> Y), is_equiv (FEmap f g).

Definition strongDFE : Type :=
  forall (X:Type) (P: X -> Type) (f g:forall x:X, P x), is_equiv (DFEmap f g).

(** Of course, strong functional extensionality implies naive
functional extensionality. *)

Theorem strongFE_implies_naiveFE : strongFE -> naiveFE.
Proof.
  intros H X Y f g.
  exact (equiv_inv (existT _ (FEmap f g) (H X Y f g))).
Defined.

Theorem strongDFE_implies_naiveDFE : strongDFE -> naiveDFE.
Proof.
  intros H X Y f g.
  exact (equiv_inv (existT _ (DFEmap f g) (H X Y f g))).
Defined.

(** We also observe that for both strong and naive functional
extensionality, the dependent version implies the non-dependent
version.  *)

Theorem strongDFE_implies_strongFE : strongDFE -> strongFE.
Proof.
  intros H X Y f g. 
  exact (H X (fun x => Y) f g).
Defined.

Theorem naiveDFE_implies_naiveFE : naiveDFE -> naiveFE.
Proof.
  intros H X Y f g.
  exact (H X (fun x => Y) f g).
Defined.


(** Can we go backwards, getting to strong functional extensionality
from naive functional extensionality?  At first the prospects don't
look good; naive functional extensionality gives us a map going
backwards, but it doesn't assert anything *about* that map, so it
seems unlikely that it would be an inverse to [FEmap].

However, it turns out that we can go backwards; the key is to first
forget down to an even weaker axiom, called "weak functional
extensionality".  This has only one version, which states that the
dependent product of a family of (continuously) contractible types is
contractible.  *)

Definition weakFE := forall (X:Type) (P: X -> Type),
  (forall x:X, contractible (P x)) -> contractible (forall x:X, P x).

(** To justify the name, we show that naive (dependent) functional
extensionality implies weak functional extensionality. *)

Theorem naiveDFE_implies_weakFE : naiveDFE -> weakFE.
Proof.
  intros H X P H1.
  exists (fun x => projT1 (H1 x)).
  intro f.
  assert (p : forall (x:X) (y:P x), y ~~> ((fun x => projT1 (H1 x)) x)).
  intros. apply H1.
  apply H. intro x. apply p.
Defined.


(** Now let's show that weak functional extensionality implies naive
(dependent) functional extensionality.  Here's the idea.  We need a
family of contractible spaces to which to apply [weak_funext].  Given
f,g dependent functions valued in [P:X->Type], we consider the family of
path spaces

  fun x => { y:P x  &   path (f x) y }

Since each of these consists of paths in some space with one fixed
endpoint, they are all contractible; thus by contr_funext their space
of sections is contractible.  But f and g both enrich naturally to
sections of this family, the one tautologically and the other via a
given homotopy between f and g.  Thus we obtain a path between the
enrichments of f and g. 

We'd like to get immediately from this to a path from f to g, but
actually what we get from it is a path between their eta expansions.
Thus, we need to assert (dependent) eta expansion as an axiom.  Eta
expansion can be regarded as "functional extensionality with respect
to definitional equality."  It implies that the contextual 1-category
of the type theory is locally cartesian closed.  (The functional
extensionality axioms are rather about local cartesian closure of the
$(\infty,1)$-category presented by the theory.) *)

Definition etaD {A} {P : A -> Type} (f : forall x, P x) := fun x => f x.

Definition etaD_statement := forall (A:Type) (P : A -> Type) (f : forall x, P x), etaD f ~~> f.

(** Here's what the definition would be, module eta. *)

Definition DFEinv_eta (weakFErule : weakFE) {A} {P : A -> Type} (f g : forall x, P x)
  (p : forall x, f x ~~> g x) : (etaD f ~~> etaD g) :=
  (map (fun K x => projT1 (K x))
    (contr_path
      (fun x => existT _ (f x) (idpath (f x)))
      (fun x => existT _ (g x) (p x))
      (weakFErule _ (fun x => { y:P x  &  (f x) ~~> y })
        (fun x => pathspace_contr (f x))))).

(** And the result of composing it with eta, which will be the actual
   inverse to DFEmap.  *)

Definition DFEinv (etaDrule : etaD_statement) (weakFErule : weakFE) {A} {P : A -> Type}
  (f g : forall x, P x) (p : forall x, f x ~~> g x) : (f ~~> g)
  := ! etaDrule _ _ f @ DFEinv_eta weakFErule f g p @ etaDrule _ _ g.

Theorem weakFE_implies_naiveDFE : etaD_statement -> weakFE -> naiveDFE.
Proof.
  intros etaDrule weakFErule.
  unfold naiveDFE; intros.
  apply DFEinv; assumption.
Defined.

(** Now let's move on to strong DFE.  The goal is to use [cmu_theorem]
with inverse map [DFEinv] constructed out of [weakFE].  This is more
promising than starting from [naiveDFE], since [weakFE] is an
assertion of contractibility (a propositition) rather than data, so we
can expect not to need any additional "coherence" axioms.

Currently, however, I also need the following "computation rule" for
the etaD axiom (which would be automatic if eta were a definitional
equality).  But I don't think VV needed this. *)

Definition etaD_computation (etaDrule : etaD_statement) :=
  forall (X:Type) (P : X -> Type) (f : forall x, P x) (x : X),
  DFEmap (etaD f) f (etaDrule X P f) x ~~> idpath (f x).

(** We need the version of the computation rule acting on the
   opposite path too. *)

Lemma etaDcomprule_opp (etaDrule : etaD_statement) (etaDcomprule : etaD_computation etaDrule)
  (X : Type) (P : X -> Type) (f: forall x:X, P x) (x : X) :
  DFEmap f (etaD f) (!etaDrule X P f) x ~~> idpath (f x).
Proof.
  intros. unfold DFEmap, etaD.
  path_via (! map (fun h => h x) (etaDrule X P f)).
  apply opposite_map with
    (f := fun h => h x)
    (p := etaDrule X P f).
  path_via (!idpath (f x)).
  apply opposite2.
  apply etaDcomprule.
Defined.

(** For ease of notation, let's open a section in which we assume
dependent eta, weak FE and the underlying type family. *)

Section weakFE_to_strongFE.

  Variable etaDrule : etaD_statement.
  Variable weakFErule : weakFE.
  Variable etaDcomprule : etaD_computation etaDrule.

  Variable X : Type.
  Variable P : X -> Type.

  Definition DFEinv_eta' := @DFEinv_eta weakFErule X P.
  Definition DFEinv' := @DFEinv etaDrule weakFErule X P.
  Definition weakFE_implies_naiveDFE' := weakFE_implies_naiveDFE etaDrule weakFErule.

  (** Here's a lemma about functoriality of the DFEmap, which is much too manual. *)

  Lemma DFEmapmap (f g h k: forall x:X, P x) (p:f ~~> g) (q : g ~~> h) (r: h ~~> k)
    : (fun x => DFEmap f g p x @ DFEmap g h q x @ DFEmap h k r x) ~~> DFEmap f k (p @ q @ r).
  Proof.
    intros.
    apply weakFE_implies_naiveDFE'.
    intro x.
    unfold DFEmap.
    path_via ((map (fun h0 : forall x0 : X, P x0 => h0 x) (p @ q)) @
      map (fun h0 : forall x0 : X, P x0 => h0 x) r).
    apply opposite. 
    apply concat_map with
      (f := (fun h0 : forall x0 : X, P x0 => h0 x)).
    path_via (map (fun h0 : forall x0 : X, P x0 => h0 x) ((p @ q) @ r)).
    apply opposite.
    apply concat_map with
      (f := (fun h0 : forall x0 : X, P x0 => h0 x)).
  Defined.
  
  (** Now let's prove that [DFEinv] is a section of [DFEmap].  The
  idea here is that the construction of [DFEinv] went through a path
  in the space of sections of our family of contractible types, but we
  just projected away part of that data in constructing [DEFinv].  Now
  we want to look at the rest of it. *)

  Lemma DFEinv_section (f g : forall x, P x) (p:forall x, f x ~~> g x) :
    DFEmap f g (DFEinv' f g p) ~~> p.
  Proof.
    intros f g p.
    unfold DFEinv.
    (** First we get rid of the etas. *)
    path_via (fun x =>
      (DFEmap f (etaD f) (!etaDrule X P f) x) @
      (DFEmap (etaD f) (etaD g) (DFEinv_eta' f g p) x) @
      (DFEmap (etaD g) g (etaDrule X P g)) x).
    apply opposite.
    apply DFEmapmap.
    apply weakFE_implies_naiveDFE'.
    intro x.
    path_via ((DFEmap f (etaD f) (!etaDrule X P f) x @
      DFEmap (etaD f) (etaD g) (DFEinv_eta' f g p) x) @
    idpath (g x)).
    (* apply etaDcomprule. *)
    path_via (DFEmap f (etaD f) (!etaDrule X P f) x @
      DFEmap (etaD f) (etaD g) (DFEinv_eta' f g p) x).
    path_via (idpath (f x) @
      DFEmap (etaD f) (etaD g) (DFEinv_eta' f g p) x).
    apply etaDcomprule_opp; assumption.
    path_via (DFEmap (etaD f) (etaD g) (DFEinv_eta' f g p) x).
    (** We define [sectp] to be the path in the space of sections referred to above. *)
    set (sectp := contr_path
      (fun x => existT _ (f x) (idpath (f x)))
      (fun x => existT _ (g x) (p x))
      (weakFErule X (fun x => { y:P x  &  (f x) ~~> y })
        (fun x => pathspace_contr (f x)))).
    unfold etaD, DFEmap.
    (* The domain of the path we want is obtained by mapping [sectp]
       along "compose with [projT1]" and then along "evaluate at [x]".  Our
       first job is to reverse the order of those mappings to be first
       "evaluate at [x]" and then "[projT1]". *)
    path_via (map (fun K => projT1 (K x)) sectp).
    apply opposite.
    apply composition_map with
      (f := fun K x0 => projT1 (K x0))
      (g := fun h => h x)
      (p := sectp).
    path_via (map (@projT1 _ _) (map (fun h => h x) sectp)).
    apply composition_map with
      (f := fun h => h x)
      (g := @projT1 _ _)
      (p := sectp).
    (* Now we want to use the second half of [sectp], but the messy
       piece doesn't quite look like what the output of that yet
       Nevertheless, let's peel that bit off and see what's left.  *)
    apply (fun q => q @ (map_dep
      (P := fun q => f x ~~> projT1 q)
      (@projT2 _ _)
      (map (fun h : forall x0 : X, {y : P x0 &  f x0 ~~> y} => h x) sectp))).
    (* This is starting to look promising; now we want to turn that
       transport into a concatenation with [trans_is_concat] so we can get
       rid of that [idpath].  Here's what that gets us. *)
    path_via (idpath (f x) @ (map (@projT1 _ _)
      (map (fun h : forall x0 : X, {y : P x0 &  f x0 ~~> y} => h x) sectp))).
    path_via (transport
      (map (@projT1 _ _)
        (map (fun h : forall x0 : X, {y : P x0 &  f x0 ~~> y} => h x) sectp))
      (idpath (f x))).
    apply opposite, trans_is_concat.
    (* We're left with an instance of [map_trans]. *)
    exact (!map_trans
      (fun y => f x ~~> y)
      (@projT1 _ _)
      (map (fun h : forall x0 : X, {y : P x0 &  f x0 ~~> y} => h x) sectp)
      (idpath (f x))).
  Defined.

  (** Now we need to show the reverse, that [DFEinv] is a retraction
  of [DFEmap].  The idea here is that [DFEinv f g p] is obtained by
  first "packing" [f], [g], and [p] into a "function equipped with a
  (pointwise) homotopy to [f]" and then applying some construction to
  it.  But we can also "pack" [f], [f], and the identity into a
  similar object, which can be shown to evaluate back to the identity
  path of [f].

  Moreover, if [p] was given as a path [f ~~> g] rather than a
  pointwise homotopy, then these two objects are connected by a path
  which incorporates [p].  Applying the construction of [DFEinv]
  pathwise to this path, we obtain a commutative triangle composed of
  the identity of [f], the path [p], and its image under [DFEinv o
  DFEmap].  This gives the desired result.

  The following functions do this "packing".  *)

  Definition weakFE_pack (f g : forall x, P x) (p : f ~~> g) :
    { h : forall x, P x  &  forall x, f x ~~> h x}
    := existT _ (etaD g) (DFEmap _ _ p).

  Definition weakFE_packpath (f g : forall x, P x) (p : f ~~> g) :
    weakFE_pack f f (idpath f) ~~> weakFE_pack f g p.
  Proof.
    intros f g p.
    apply total_paths with (p := map etaD p). simpl.
    induction p; auto.
    (* This definition ought to work with [p] only of type [etaD f ~~>
       etaD g], but it gives weird error messages "X ought to be of
       type Z, but instead it is of type Z." *)
  Defined.

  (** The next lemma says that if we construct a path in the total
  space of a fibration using [total_paths], then project it down to
  the base, we end up with the same path in the base that we started
  with as input to [total_paths]. *)

  Lemma total_paths_base (A:Type) (P : A -> Type)
    (x y : A) (x': P x) (y': P y) (p: x ~~> y) (q : transport p x' ~~> y') :
    map (fun z => projT1 z) (total_paths A P (existT _ x x') (existT _ y y') p q)  ~~> p.
  Proof.
    intros. 
    induction p. simpl in q.
    induction q. auto.
  Defined.

  (** Finally, this lemma is the special case of the desired result,
  acting on an identity path. *)

  Lemma DFEinv_eta_id (f : forall x, P x):
    DFEinv_eta' f (etaD f) (DFEmap _ _ (idpath f)) ~~> idpath (etaD f).
  Proof.
    intro f.
    unfold DFEinv_eta', DFEinv_eta. simpl.
    path_via (map (fun (K : forall x : X, {y : P x &  f x ~~> y}) (x : X) => projT1 (K x))
      (idpath (fun x => existT _ (f x) (idpath (f x))))).
    apply map.
    apply contr_path2.
    exact (weakFErule X _ (fun x => pathspace_contr (f x))).
  Defined.

  (** Now we're ready for the retraction theorem. *)

  Lemma DFEinv_retraction (f g : forall x, P x) (p : f ~~> g) :
    DFEinv' f g (DFEmap f g p) ~~> p.
  Proof.
    intros f g p.
    unfold DFEinv', DFEinv.
    (** Again, our first job is to get rid of the etas, using naturality. *)
    path_via (!etaDrule X P f @ (DFEinv_eta' f g (DFEmap f g p) @ etaDrule X P g)).
    apply concat_associativity.
    apply concat_moveleft_onleft.
    path_via (map etaD p @ etaDrule X P g).

    (** Here's the packed path between [f] and [g]. *)
    set (ppack := weakFE_packpath f g p).
    (** Now we engage in a bit of forward reasoning.  First we apply
    [DFEinv_eta] to the homotopies in the packed [f] and [g]. *)
    set (dfeinv_ppack := map
      (fun pack => (existT (fun h => etaD f ~~> etaD h)
        (projT1 pack)
        (DFEinv_eta' f (projT1 pack) (projT2 pack))))
      ppack).
    simpl in dfeinv_ppack.
    (** Now we compose that with a path which is essentially the identity of [f], packed. *)
    set (dfeinv_ppack_id := (total_paths _ _
      (existT (fun h : forall x : X, P x => etaD f ~~> etaD h) 
        (etaD f) (idpath (etaD f)))
      (existT (fun h : forall x : X, P x => etaD f ~~> etaD h) 
        (etaD f) (DFEinv_eta' f (etaD f) (DFEmap _ _ (idpath f))))
      (idpath _)
      (!DFEinv_eta_id f))
    @ dfeinv_ppack).
    simpl in dfeinv_ppack_id.
    (** Now we invert the path between [f] and [g], for technical reasons. *)
    set (dfeinv_ppack_id_inv := map
      (fun pack => existT (fun h => etaD h ~~> etaD f) (projT1 pack) (!projT2 pack))
      dfeinv_ppack_id).
    simpl in dfeinv_ppack_id_inv.
    (** And finally we can extract the triangle referred to above. *)
    set (triangle := @hfiber_triangle _ _ etaD (etaD f) _ _ dfeinv_ppack_id_inv).
    simpl in triangle.

    (** Now we have to massage our goal into a form where we can apply
    that triangle. *)
    path_via (map etaD (map etaD p)).
    path_via (map etaD (map (@projT1 _ _) dfeinv_ppack_id_inv)).
    path_via (!! DFEinv_eta' f g (DFEmap f g p)).
    path_via (idpath _ @ !! DFEinv_eta' f g (DFEmap f g p)).
    apply concat_moveleft_onright.
    apply opposite.
    (** Ah, that looks more like it.  It doesn't look exactly the
    same, but since [etaD] is idempotent, it is the same. *)
    path_via (map etaD (map (@projT1 _ _) dfeinv_ppack_id_inv)
      @ !DFEinv_eta' f (etaD g) (DFEmap f g p)).

    (** Oops, what's left?  We incurred some extra obligations. *)
    apply map, opposite.
    (** This goal wants to know that the first half of the "packed"
    path is actually the path [p] we started with (up to eta).  I
    guess now we need to do some "unpacking". *)
    path_via (map (fun pack => projT1 pack) dfeinv_ppack_id).
    unfold dfeinv_ppack_id.
    path_via (map (fun pack => projT1 pack)
      (total_paths _ _
        (existT _ (etaD f) (idpath (etaD f)))
        (existT _ (etaD f) (DFEinv_eta' f (etaD f) (DFEmap _ _ (idpath f))))
        (idpath (projT1 (existT _ (etaD f) (idpath (etaD f)))))
        (!DFEinv_eta_id f))
      @
      map (fun pack => projT1 pack) dfeinv_ppack).
    path_via ((idpath (projT1 (existT _ (etaD f) (idpath (etaD f)))))
      @
      (map (fun pack => projT1 pack) dfeinv_ppack)).
    path_via (map (fun pack => projT1 pack) dfeinv_ppack).
    unfold dfeinv_ppack.
    path_via (map (fun pack => projT1 pack) ppack).
    unfold ppack, weakFE_packpath.
    (** Ugh, 6 subgoals!  But we can knock them out quickly now. *)
    apply opposite, total_paths_base.
    apply composition_map with
      (f := fun pack => existT _ (projT1 pack)
        (DFEinv_eta' f (projT1 pack) (projT2 pack)))
      (g := fun pack => projT1 pack)
      (p := ppack).
    apply opposite, total_paths_base.
    apply opposite, concat_map.
    apply composition_map with
      (g := @projT1 _ _)
      (f := (fun pack : {h : forall x : X, P x &  etaD f ~~> etaD h} =>
        existT (fun h : forall x : X, P x => etaD h ~~> etaD f)
        (projT1 pack) (!projT2 pack)))
      (p := dfeinv_ppack_id).
    (** This final subgoal is just idempotence of [etaD]. *)
    apply opposite. apply composition_map with
      (f := etaD) (g := etaD) (p := p).
    (** Hooray! *)
  Defined.

End weakFE_to_strongFE.

Theorem weakFE_implies_strongFE (etaDrule : etaD_statement) :
  etaD_computation etaDrule -> weakFE -> strongDFE.
Proof.
  intros etaDrule etaDcomprule weakFErule. unfold strongDFE.
  intros X P f g.
  apply adjoint_to_equiv, adjointify.
  exists (DFEinv etaDrule weakFErule f g). 
  split.
  apply DFEinv_section; assumption. apply DFEinv_retraction.
Defined.
