Inductive nh : Set :=
  | O : nh
  | S : nh -> nh
  | H : nh -> nh.

Axiom sh_equiv : forall (a : nh), S (H a) = H (S a).

Fixpoint addnh (a b : nh) :=
  match a with
  | O => b
  | S a' => S (addnh a' b)
  | H a' => H (addnh a' b)
  end.

Lemma addnh_O_b : forall (b : nh), addnh O b = b.
  reflexivity.
  Defined.

Lemma addnh_Sa_b : forall (a b : nh), addnh (S a) b = S (addnh a b).
  reflexivity.
  Defined.

Lemma addnh_Ha_b : forall (a b : nh), addnh (H a) b = H (addnh a b).
  reflexivity.
  Defined.

Lemma addnh_a_O : forall (a : nh), addnh a O = a.
  induction a.
    rewrite addnh_O_b; reflexivity.
    rewrite addnh_Sa_b; rewrite IHa; reflexivity.
    rewrite addnh_Ha_b; rewrite IHa; reflexivity.
  Defined.

Lemma addnh_a_Sb : forall (a b : nh), addnh a (S b) = S (addnh a b).
  induction a; intros b.
    rewrite ?addnh_O_b; reflexivity.
    rewrite ?addnh_Sa_b; rewrite IHa; reflexivity.
    rewrite ?addnh_Ha_b; rewrite IHa; rewrite sh_equiv; reflexivity.
  Defined.

Lemma addnh_a_Hb : forall (a b : nh), addnh a (H b) = H (addnh a b).
  induction a; intros b.
    rewrite ?addnh_O_b; reflexivity.
    rewrite ?addnh_Sa_b; rewrite IHa; rewrite sh_equiv; reflexivity.
    rewrite ?addnh_Ha_b; rewrite IHa; reflexivity.
  Defined.

Lemma addnh_comm : forall (a b : nh), addnh a b = addnh b a.
  induction a; intros b.
  rewrite addnh_a_O; rewrite addnh_O_b; reflexivity.
  rewrite addnh_Sa_b; rewrite addnh_a_Sb; rewrite IHa; reflexivity.
  rewrite addnh_Ha_b; rewrite addnh_a_Hb; rewrite IHa; reflexivity.
  Defined.

Lemma addnh_assoc : forall (a b c : nh), addnh a (addnh b c) = addnh (addnh a b) c.
  induction a; intros b c.
    rewrite ?addnh_O_b; reflexivity.
    rewrite ?addnh_Sa_b; rewrite IHa; reflexivity.
    rewrite ?addnh_Ha_b; rewrite IHa; reflexivity.
  Defined.

Fixpoint mlh (a : nh) :=
  match a with
  | O => O
  | S a' => addnh (H O) (mlh a')
  | H a' => mlh a'
  end.

Fixpoint mulnh (a b : nh) :=
  match a with
  | O => O
  | H a' => addnh (mlh b) (mulnh a' b)
  | S a' => addnh b (mulnh a' b)
  end.

Lemma mlh_eq_mulnh_HO_b : 
  