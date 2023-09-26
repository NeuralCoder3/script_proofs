Load tactics.

(*
3.20 (page 86)
*)
Example E3_20 Object (P Q:Object*Object->Prop):
    (forall x y, P(x,y) -> Q(y,x)) /\ (forall x, P(x,x)) -> forall y, Q(y,y).
Proof.
    impl_intro.
    and_elim H0.
    forall_intro z.
    forall_elim H1 z.
    forall_elim H3 z.
    impl_apply H4.
    forall_elim H2 z.
    assumption H5.
Restart. (* lets try it with Coq tactics *)
    intros [H1 H2] y.
    apply H1.
    apply H2.
Qed.


(*
3.30 (page 92)
*)
Example E3_30: forall (x:nat), x <= x.
Proof.
    forall_intro x.
    exists_intro 0.
    axiom add_0_r.
    forall_elim A0 x.
    equals_elim H0.
    equals_intro.
Restart.
    intros x.
    unfold leq.
    exists 0.
    lia.
Qed.

(*
3.33 (page 94)
*)
Goal forall x y, even(x) -> even(y) -> even(x+y).
Proof.
    forall_intro x.
    forall_intro y.
    impl_intro.
    impl_intro.
    defn even.
    exists_elim H0 k1.
    exists_elim H1 k2.
    exists_intro (k1+k2).
    axiom mul_add_distr_l.
    forall_elim A0 2.
    forall_elim H4 k1.
    forall_elim H5 k2.
    equals_elim H6.
    equals_elim_rev H2.
    equals_elim_rev H3.
    equals_intro.
Restart.
    intros x y Hx Hy.
    destruct Hx as [k1 Hk1].
    destruct Hy as [k2 Hk2].
    exists (k1+k2).
    rewrite Hk1, Hk2.
    lia.
Qed.


(*
For more examples see 2022/script.v
*)