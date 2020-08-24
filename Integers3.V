(* naturals, addition & multiplication *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint addn (n1 n2 : nat) :=
  match n1 with
  | O => n2
  | S n1' => S (addn n1' n2)
  end.

Lemma addn_O_m : forall (m : nat), addn O m = m.
  reflexivity.
  Defined.

Lemma addn_n_O : forall (n : nat), addn n O = n.
  induction n; try reflexivity.
  simpl; rewrite IHn; reflexivity.
  Defined.

Lemma addn_Sn_m : forall (n m : nat), addn (S n) m = S (addn n m).
  reflexivity.
  Defined.

Lemma addn_n_Sm : forall (n m : nat), addn n (S m) = S (addn n m).
  induction n; try reflexivity.
  intros m. rewrite ?addn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma addn_S_comm : forall (n m : nat), addn n (S m) = addn (S n) m.
  intros n m.
  rewrite addn_Sn_m. rewrite addn_n_Sm. 
  reflexivity. Defined.

Theorem addn_comm : forall (n m : nat), addn n m = addn m n.
  induction n.
  simpl. intros m. rewrite addn_n_O. reflexivity.
  intros m. rewrite addn_Sn_m. rewrite addn_n_Sm.
  rewrite IHn. reflexivity.
  Defined.

Theorem addn_assoc : forall (n m o : nat), addn (addn n m) o = addn n (addn m o).
  induction n; destruct m; destruct o; 
  try reflexivity;
  try (rewrite ?addn_n_O; rewrite ?addn_O_n; reflexivity).
  rewrite ?addn_Sn_m. rewrite ?addn_n_Sm. rewrite addn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Fixpoint muln (n1 n2 : nat) :=
  match n1 with
  | O => O
  | S n1' => addn n2 (muln n1' n2)
  end.

Lemma muln_n_O : forall (n : nat), muln n O = O.
  induction n; try reflexivity.
  simpl.
  assumption.
  Defined.

Lemma muln_O_m : forall (m : nat), muln O m = O.
  reflexivity.
  Defined.

Lemma muln_Sn_m : forall (n m : nat), muln (S n) m = addn m (muln n m).
  reflexivity.
  Defined.

Lemma muln_n_Sm : forall (n m : nat), muln n (S m) = addn n (muln n m).
  induction n; try reflexivity.
  intros m. simpl.
  rewrite IHn.
  rewrite <- ?addn_assoc.
  rewrite (addn_comm m n).
  reflexivity.
  Defined.

Lemma muln_n_SO : forall (n : nat), muln n (S O) = n.
  induction n; try reflexivity.
  rewrite muln_n_Sm. rewrite muln_n_O. rewrite addn_n_O. reflexivity.
  Defined.

Lemma muln_SO_m : forall (m : nat), muln (S O) m = m.
  induction m; try reflexivity.
  rewrite muln_Sn_m. rewrite muln_O_m. rewrite addn_n_O. reflexivity.
  Defined. 

Theorem muln_comm : forall (n m : nat), muln n m = muln m n.
  induction n; destruct m; try reflexivity;
  try (rewrite ?muln_n_O; rewrite ?muln_O_m; reflexivity).
  rewrite ?muln_Sn_m. rewrite ?muln_n_Sm.
  rewrite ?addn_Sn_m. rewrite IHn.
  rewrite <- ?addn_assoc. rewrite (addn_comm m n). reflexivity.
  Defined.

Lemma addn_addn_nm_no : forall (n m o : nat), addn n (addn n (addn m o)) = addn (addn n m) (addn n o).
  intros n m o.
  rewrite addn_assoc.
  rewrite <- (addn_assoc m n o).
  rewrite (addn_comm m n).
  rewrite addn_assoc.
  reflexivity.
  Defined.

Theorem muln_addn : forall (n m o : nat), muln (addn n m) o = addn (muln n o) (muln m o).
  induction n; destruct m; destruct o; try reflexivity;
  try (rewrite ?muln_n_O; rewrite ?muln_O_m; reflexivity).
  rewrite ?muln_O_m. rewrite ?addn_n_O. reflexivity.
  rewrite addn_Sn_m. rewrite addn_n_Sm.
  rewrite muln_Sn_m. rewrite muln_Sn_m.
  rewrite IHn.
  rewrite ?muln_Sn_m.
  rewrite addn_addn_nm_no.
  reflexivity.
  Defined.

Lemma muln_addn_r : forall (n m o : nat), muln n (addn m o) = addn (muln n m) (muln n o).
  intros n m o.
  rewrite muln_comm.
  rewrite muln_addn.
  rewrite (muln_comm m n). rewrite (muln_comm o n).
  reflexivity.
  Defined.

Theorem muln_assoc : forall (n m o : nat), muln (muln n m) o = muln n (muln m o).
  induction n.
  reflexivity.
  simpl. intros m o.
  rewrite ?muln_addn_r. rewrite muln_addn.
  rewrite IHn.
  reflexivity.
  Defined.

(* integers, addition, subtraction, multiplication. *)
Inductive int : Set :=
  | P : nat -> int
  | N : nat -> int.

Axiom pz_equals_nz : P O = N O.

Fixpoint neg (i : int) :=
  match i with
  | P O => P O
  | P n => N n
  | N n => P n
  end.

Lemma neg_Pn : forall (n : nat), neg (P n) = N n.
  destruct n; try reflexivity. 
  rewrite <- pz_equals_nz.
  reflexivity.
  Defined.

Lemma neg_Nn : forall (n : nat), neg (N n) = P n.
  reflexivity.
  Defined.

Lemma neg_neg : forall (i : int), neg (neg i) = i.
  destruct i; destruct n; try (rewrite <- pz_equals_nz); reflexivity.
  Defined.

Fixpoint inci (i : int) :=
  match i with
  | P n => P (S n)
  | N O => P (S O)
  | N (S n) => N n
  end.

Fixpoint deci (i : int) :=
  match i with
  | P O => N (S O)
  | P (S n) => P n
  | N n => N (S n)
  end.

Lemma inci_Pn : forall (n : nat), inci (P n) = P (S n).
  reflexivity.
  Defined.

Lemma inci_NSn : forall (n : nat), inci (N (S n)) = N n.
  reflexivity.
  Defined.

Lemma deci_PSn : forall (n : nat), deci (P (S n)) = P n.
  reflexivity.
  Defined.

Lemma deci_Nn : forall (n : nat), deci (N n) = N (S n).
  reflexivity.
  Defined.

Lemma neg_inci : forall (i : int), neg (inci i) = deci (neg i).
  destruct i; destruct n; try reflexivity.
  Defined.

Lemma neg_deci : forall (i : int), neg (deci i) = inci (neg i).
  destruct i; destruct n; try reflexivity.
  rewrite deci_PSn.
  rewrite ?neg_Pn.
  rewrite inci_NSn.
  reflexivity.
  Defined.

Lemma inci_deci : forall (i : int), inci (deci i) = i.
  destruct i; induction n; try reflexivity.
  simpl. rewrite pz_equals_nz. reflexivity.
  Defined.

Lemma deci_inci : forall (i : int), deci (inci i) = i.
  destruct i; induction n; try reflexivity.
  simpl. rewrite pz_equals_nz. reflexivity.
  Defined.

(* sub functions created to prevent inductive case troubles in addi,  subi *)

Fixpoint sub_PPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => 
    match n2 with
    | O => P n1
    | S n2' => sub_PPn n1' n2'
    end
  end.

Lemma subPPn_O_m : forall (m : nat), sub_PPn O m = N m.
  reflexivity.
  Defined.

Lemma subPPn_n_O : forall (n : nat), sub_PPn n O = P n.
  destruct n.
  simpl. rewrite pz_equals_nz; reflexivity.
  reflexivity.
  Defined.

Lemma subPPn_Sn_Sm : forall (n m : nat), sub_PPn (S n) (S m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma subPPn_n_n : forall (n : nat), sub_PPn n n = P O.
  induction n.
  simpl; rewrite ?pz_equals_nz; try reflexivity.
  simpl. assumption.
  Defined.

Lemma subPPn_Sn_m : forall (n m : nat), sub_PPn (S n) m = inci (sub_PPn n m).
  induction n.
  intros m.
  rewrite subPPn_O_m.
  destruct m; reflexivity.
  destruct m. rewrite ?subPPn_n_O.
  reflexivity.
  rewrite ?subPPn_Sn_Sm.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPPn_n_Sm : forall (n m : nat), sub_PPn n (S m) = deci (sub_PPn n m).
  induction n.
  intros m.
  rewrite ?subPPn_O_m.
  destruct m; reflexivity.
  destruct m. rewrite ?subPPn_n_O.
  rewrite subPPn_Sn_Sm. rewrite subPPn_n_O.
  rewrite deci_PSn.
  reflexivity.
  rewrite ?subPPn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subPPn_anticomm : forall (n m : nat), sub_PPn n m = neg (sub_PPn m n).
  induction n.
  intros m. 
  rewrite subPPn_n_O. rewrite subPPn_O_m.
  rewrite neg_Pn. reflexivity.
  intros m. 
  rewrite subPPn_Sn_m. rewrite subPPn_n_Sm.
  rewrite neg_deci.
  rewrite IHn.
  reflexivity.
  Defined.

Fixpoint sub_PNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' => inci (sub_PNn n1' n2)
  end.

Lemma subPNn_n_O : forall (n : nat), sub_PNn n O = P n.
  induction n; try reflexivity.
  simpl. rewrite IHn.
  rewrite inci_Pn.
  reflexivity.
  Defined.

Lemma subPNn_O_m : forall (m : nat), sub_PNn O m = P m.
  reflexivity.
  Defined.

Lemma subPNn_Sn_m : forall (n m : nat), sub_PNn (S n) m = inci (sub_PNn n m).
  reflexivity.
  Defined.

Lemma subPNn_n_Sm : forall (n m : nat), sub_PNn n (S m) = inci (sub_PNn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subPNn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma subPNn_eq_Paddn : forall (n m : nat), sub_PNn n m = P (addn n m).
  induction n. try reflexivity.
  intros m. rewrite ?subPNn_Sn_m.
  rewrite IHn. rewrite addn_Sn_m.
  rewrite inci_Pn.
  reflexivity.
  Defined.

Fixpoint sub_NPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => deci (sub_NPn n1' n2)
  end.

Lemma subNPn_n_O : forall (n : nat), sub_NPn n O = N n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite deci_Nn.
  reflexivity.
  Defined.

Lemma subNPn_O_m : forall (m : nat), sub_NPn O m = N m.
  reflexivity.
  Defined.

Lemma subNPn_Sn_m : forall (n m : nat), sub_NPn (S n) m = deci (sub_NPn n m).
  reflexivity.
  Defined.

Lemma subNPn_n_Sm : forall (n m : nat), sub_NPn n (S m) = deci (sub_NPn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subNPn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNPn_eq_Naddn : forall (n m : nat), sub_NPn n m = N (addn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subNPn_Sn_m.
  simpl.
  rewrite IHn.
  rewrite deci_Nn.
  reflexivity.
  Defined.

Fixpoint sub_NNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' =>
    match n2 with
    | O => N n1
    | S n2' => sub_NNn n1' n2'
    end
  end.

Lemma subNNn_n_O : forall (n : nat), sub_NNn n O = N n.
  induction n; try reflexivity.
  simpl; rewrite pz_equals_nz; reflexivity.
  Defined.

Lemma subNNn_O_m : forall (m : nat), sub_NNn O m = P m.
  reflexivity.
  Defined.

Lemma subNNn_Sn_Sm : forall (n m : nat), sub_NNn (S n) (S m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma subNNn_n_Sm : forall (n m : nat), sub_NNn n (S m) = inci (sub_NNn n m).
  induction n; try reflexivity.
  destruct m.
  rewrite subNNn_n_O. simpl.
  rewrite subNNn_n_O. reflexivity.
  rewrite ?subNNn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNNn_Sn_m : forall (n m : nat), sub_NNn (S n) m = deci (sub_NNn n m).
  induction n; try reflexivity.
  destruct m; try reflexivity.
  rewrite ?subNNn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNNn_n_n : forall (n : nat), sub_NNn n n = P O.
  induction n; try reflexivity.
  rewrite subNNn_Sn_Sm. assumption.
  Defined.

Lemma subNNn_anticomm : forall (n m : nat), sub_NNn n m = neg (sub_NNn m n).
  induction n; intros m.
  rewrite subNNn_O_m; rewrite subNNn_n_O.
  rewrite neg_Nn.
  reflexivity.
  rewrite subNNn_Sn_m. rewrite subNNn_n_Sm.
  rewrite neg_inci.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPPn_neg_subNNn : forall (n m : nat), sub_PPn n m = neg (sub_NNn n m).
  induction n; destruct m; try reflexivity.
  simpl; rewrite pz_equals_nz; try reflexivity.
  rewrite subPPn_Sn_Sm.
  rewrite subNNn_Sn_Sm.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPNn_neg_subNPn : forall (n m : nat), sub_PNn n m = neg (sub_NPn n m).
  induction n; destruct m; try reflexivity.
  simpl. rewrite subPNn_n_O. rewrite subNPn_n_O. simpl. reflexivity.
  rewrite ?subPNn_Sn_m; rewrite ?subNPn_Sn_m.
  rewrite ?subPNn_n_Sm; rewrite ?subNPn_n_Sm.
  rewrite IHn.
  rewrite ?neg_deci.
  reflexivity.
  Defined.

Fixpoint subi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PPn n1 n2
  | P n1, N n2 => sub_PNn n1 n2
  | N n1, P n2 => sub_NPn n1 n2
  | N n1, N n2 => sub_NNn n1 n2
  end.

Fixpoint addi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PNn n1 n2
  | P n1, N n2 => sub_PPn n1 n2
  | N n1, P n2 => sub_NNn n1 n2
  | N n1, N n2 => sub_NPn n1 n2
  end.

Lemma addi_PP : forall (n m : nat), addi (P n) (P m) = sub_PNn n m.
  reflexivity.
  Defined.

Lemma addi_PN : forall (n m : nat), addi (P n) (N m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma addi_NP : forall (n m : nat), addi (N n) (P m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma addi_NN : forall (n m : nat), addi (N n) (N m) = sub_NPn n m.
  reflexivity.
  Defined.

Lemma subi_PP : forall (n m : nat), subi (P n) (P m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma subi_PN : forall (n m : nat), subi (P n) (N m) = sub_PNn n m.
  reflexivity.
  Defined.

Lemma subi_NP : forall (n m : nat), subi (N n) (P m) = sub_NPn n m.
  reflexivity.
  Defined.

Lemma subi_NN : forall (n m : nat), subi (N n) (N m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma addi_i_PO : forall (i : int), addi i (P O) = i.
  destruct i.
  rewrite addi_PP. rewrite subPNn_n_O. reflexivity.
  rewrite addi_NP. rewrite subNNn_n_O. reflexivity.
  Defined.

Lemma addi_PO_j : forall (j : int), addi (P O) j = j.
  destruct j.
  rewrite addi_PP. rewrite subPNn_O_m. reflexivity.
  rewrite addi_PN. rewrite subPPn_O_m. reflexivity.
  Defined.

Lemma subi_i_PO : forall (i : int), subi i (P O) = i.
  destruct i.
  rewrite subi_PP. rewrite subPPn_n_O. reflexivity.
  rewrite subi_NP. rewrite subNPn_n_O. reflexivity.
  Defined.

Lemma subi_PO_j : forall (j : int), subi (P O) j = neg j.
  destruct j.
  rewrite subi_PP. rewrite subPPn_O_m. rewrite neg_Pn. reflexivity.
  rewrite subi_PN. rewrite subPNn_O_m. reflexivity.
  Defined.

Lemma addiPP_eq_Paddn : forall (n m : nat), addi (P n) (P m) = P (addn n m).
  intros n m; rewrite addi_PP; rewrite subPNn_eq_Paddn; reflexivity.
  Defined.

Lemma addiNN_eq_Naddn : forall (n m : nat), addi (N n) (N m) = N (addn n m).
  intros n m; rewrite addi_NN; rewrite subNPn_eq_Naddn; reflexivity.
  Defined.

Lemma addi_Nn_Pn : forall (n : nat), addi (N n) (P n) = P O.
  intros n; rewrite addi_NP; rewrite subNNn_n_n; reflexivity.
  Defined.

Lemma addi_Pn_Nn : forall (n : nat), addi (P n) (N n) = P O.
  intros n; rewrite addi_PN; rewrite subPPn_n_n; reflexivity.
  Defined.

Lemma addi_i_negi : forall (i : int), addi i (neg i) = P O.
  destruct i;
  rewrite ?neg_Pn; rewrite ?neg_Nn;
  rewrite ?addi_Nn_Pn; rewrite ?addi_Pn_Nn;
  reflexivity.
  Defined.

Lemma subi_i_i : forall (i : int), subi i i = P O.
  destruct i.
  rewrite subi_PP. rewrite subPPn_n_n. reflexivity.
  rewrite subi_NN. rewrite subNNn_n_n. reflexivity.
  Defined.

Lemma addi_PSn_j : forall (n : nat) (j : int), addi (P (S n)) j = inci (addi (P n) j).
  destruct j as [m|m]; try reflexivity.
  rewrite ?addi_PN. rewrite subPPn_Sn_m. reflexivity.
  Defined.

Lemma addi_NSn_j : forall (n : nat) (j : int), addi (N (S n)) j = deci (addi (N n) j).
  destruct j as [m|m]; try reflexivity.
  rewrite ?addi_NP. rewrite subNNn_Sn_m. reflexivity.
  Defined.

Lemma addi_i_PSm : forall (i : int) (m : nat), addi i (P (S m)) = inci (addi i (P m)).
  destruct i as [n|n].
  intros m; rewrite ?addi_PP. rewrite subPNn_n_Sm. reflexivity.
  intros m; rewrite ?addi_NP. rewrite subNNn_n_Sm. reflexivity.
  Defined.

Lemma addi_i_NSm : forall (i : int) (m : nat), addi i (N (S m)) = deci (addi i (N m)).
  destruct i as [n|n].
  intros m; rewrite ?addi_PN. rewrite subPPn_n_Sm. reflexivity.
  intros m; rewrite ?addi_NN. rewrite subNPn_n_Sm. reflexivity.
  Defined.

Lemma addi_rel_subi : forall (i j : int), addi i j = subi i (neg j).
  destruct i as [n|n]; destruct j as [m|m]; try reflexivity.
  rewrite neg_Pn. rewrite addi_PP. rewrite subi_PN. reflexivity.
  rewrite neg_Pn. rewrite addi_NP. rewrite subi_NN. reflexivity.
  Defined.

Lemma subi_rel_addi : forall (i j : int), subi i j = addi i (neg j).
  intros i j. rewrite <- (neg_neg j).
  rewrite <- addi_rel_subi. rewrite neg_neg.
  reflexivity.
  Defined.

Lemma subi_PSn_j : forall (n : nat) (j : int), subi (P (S n)) j = inci (subi (P n) j).
  intros. rewrite -> ?subi_rel_addi.
  destruct j as [m|m]. 
  rewrite neg_Pn. rewrite addi_PSn_j. reflexivity.
  rewrite neg_Nn. rewrite addi_PSn_j. reflexivity.
  Defined.

Lemma subi_NSn_j : forall (n : nat) (j : int), subi (N (S n)) j = deci (subi (N n) j).
  intros. rewrite -> ?subi_rel_addi.
  destruct j as [m|m].
  rewrite neg_Pn. rewrite addi_NSn_j. reflexivity.
  rewrite neg_Nn. rewrite addi_NSn_j. reflexivity.
  Defined.

Lemma subi_i_PSn : forall (i : int) (m : nat), subi i (P (S m)) = deci (subi i (P m)).
  intros. rewrite -> ?subi_rel_addi.
  rewrite ?neg_Pn. rewrite addi_i_NSm. reflexivity.
  Defined.

Lemma subi_i_NSn : forall (i : int) (m : nat), subi i (N (S m)) = inci (subi i (N m)).
  intros. rewrite -> ?subi_rel_addi.
  rewrite ?neg_Nn. rewrite addi_i_PSm. reflexivity.
  Defined.

Lemma addi_inci_j : forall (i j : int), addi (inci i) j = inci (addi i j).
  destruct i as [n|n]; destruct j as [m|m]; try reflexivity;
  destruct n;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  try reflexivity.
  Defined.

Lemma addi_i_incj : forall (i j : int), addi i (inci j) = inci (addi i j).
  destruct i as [n|n]; destruct j as [m|m]; try reflexivity;
  induction n;
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  try reflexivity.
  rewrite IHn. reflexivity.
  rewrite IHn. rewrite deci_inci. reflexivity.
  Defined.

Lemma addi_deci_j : forall (i j : int), addi (deci i) j = deci (addi i j).
  destruct i as [n|n]; destruct j as [m|m]; try reflexivity;
  induction n;
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  try reflexivity.
  Defined.

Lemma addi_i_decj : forall (i j : int), addi i (deci j) = deci (addi i j).
  destruct i as [n|n]; destruct j as [m|m]; try reflexivity;
  induction n;
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  try reflexivity.
  rewrite IHn. rewrite inci_deci. reflexivity.
  rewrite ?IHn. reflexivity.
  Defined.

Lemma subi_i_incj : forall (i j : int), subi i (inci j) = deci (subi i j).
  intros i j. 
  rewrite ?subi_rel_addi.
  rewrite neg_inci. rewrite addi_i_decj.
  reflexivity.
  Defined.

 Lemma subi_i_decj : forall (i j : int), subi i (deci j) = inci (subi i j).
  intros i j.
  rewrite ?subi_rel_addi.
  rewrite neg_deci. rewrite addi_i_incj.
  reflexivity.
  Defined.

Lemma subi_inci_j : forall (i j : int), subi (inci i) j = inci (subi i j).
  intros i j.
  rewrite ?subi_rel_addi.
  rewrite addi_inci_j.
  reflexivity.
  Defined.

Lemma subi_deci_j : forall (i j : int),  subi (deci i) j = deci (subi i j).
  intros i j.
  rewrite ?subi_rel_addi.
  rewrite addi_deci_j.
  reflexivity.
  Defined.

Lemma neg_addi : forall (i j : int), neg (addi i j) = addi (neg i) (neg j).
  destruct i as [n|n]; destruct j as [m|m]; 
  induction n; 
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO; try reflexivity;
  rewrite ?neg_Pn; rewrite ?neg_Nn;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  rewrite ?neg_deci; rewrite ?neg_inci;
  rewrite ?IHn; rewrite ?neg_Pn; rewrite ?neg_Nn;
  try reflexivity.
  Defined.

Lemma neg_subi : forall (i j : int), neg (subi i j) = subi (neg i) (neg j).
  destruct i as [n|n]; destruct j as [m|m]; 
  induction n; 
  rewrite <- ?pz_equals_nz; rewrite ?subi_PO_j; rewrite ?subi_i_PO; try reflexivity;
  rewrite ?neg_Pn; rewrite ?neg_Nn;
  rewrite ?deci_PSn; rewrite ?deci_Nn; rewrite ?inci_Pn; rewrite ?inci_NSn;
  rewrite ?subi_PSn_j; rewrite ?subi_NSn_j; rewrite ?subi_i_PSm; rewrite ?subi_i_NSm;
  rewrite ?inci_deci; rewrite ?deci_inci;
  rewrite ?neg_deci; rewrite ?neg_inci;
  rewrite ?IHn; rewrite ?neg_Pn; rewrite ?neg_Nn;
  try reflexivity.
  Defined.

Theorem addi_comm : forall (i j : int), addi i j = addi j i.
  destruct i as [n|n]; destruct j as [m|m];
  induction n;
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO; try reflexivity;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite IHn; try reflexivity.
  Defined.

Theorem addi_negi_i : forall (i : int), addi (neg i) i = P O.
  intros i. rewrite addi_comm.
  rewrite addi_i_negi.
  reflexivity.
  Defined.

Theorem subi_anticomm : forall (i j : int), subi i j = neg (subi j i).
  intros i j.
  rewrite ?subi_rel_addi.
  destruct i as [n|n]; destruct j as [m|m];
  rewrite ?neg_Pn; rewrite ?neg_Nn;
  induction n;
  rewrite <- ?pz_equals_nz; rewrite ?addi_PO_j; rewrite ?addi_i_PO;
  rewrite ?neg_Pn; rewrite ?neg_Nn; try reflexivity;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j; rewrite ?addi_i_PSm; rewrite ?addi_i_NSm;
  rewrite ?neg_inci; rewrite ?neg_deci; try rewrite IHn; try reflexivity.
  Defined.

Theorem addi_assoc : forall (i j k : int), addi (addi i j) k = addi i (addi j k).
  destruct i as [n|n]; destruct j as [m|m]; destruct k as [o|o];
  induction n; rewrite <- ?pz_equals_nz; 
  rewrite ?addi_PO_j; rewrite ?addi_i_PO; try reflexivity;
  rewrite ?addi_PSn_j; rewrite ?addi_NSn_j;
  rewrite ?addi_inci_j; rewrite ?addi_deci_j;
  rewrite IHn; try reflexivity.
  Defined.

Theorem subi_sub1 : forall (i j k : int), subi (subi i j) k = subi i (addi j k).
  destruct i as [n|n]; destruct j as [m|m]; destruct k as [o|o];
  induction n; rewrite <- ?pz_equals_nz;
  rewrite ?subi_PO_j; rewrite ?subi_i_PO;
  rewrite ?neg_addi;
  rewrite subi_rel_addi; try reflexivity;
  rewrite <- subi_rel_addi; rewrite ?neg_Pn; rewrite ?neg_Nn;
  rewrite ?subi_PSn_j; rewrite ?subi_NSn_j;
  rewrite ?subi_inci_j; rewrite ?subi_deci_j; 
  rewrite IHn; try reflexivity.
  Defined.

Lemma addi_assochelp : forall (i j k : int), addi i (addi j k) = addi (addi i k) j.
  intros i j k.
  rewrite (addi_assoc i k j).
  rewrite (addi_comm k j).
  reflexivity.
  Defined.

Theorem subi_sub2 : forall (i j k : int), subi i (subi j k) = subi (addi i k) j.
  destruct i as [n|n]; destruct j as [m|m]; destruct k as [o|o];
  rewrite ?subi_rel_addi; rewrite ?neg_addi;
  rewrite ?neg_neg; rewrite ?neg_Pn; rewrite ?neg_Nn;
  rewrite addi_assochelp; try reflexivity.
  Defined.

Lemma addi_subi : forall (i j : int), addi (subi i j) j = i.
  intros i j. rewrite subi_rel_addi.
  rewrite addi_assoc. rewrite addi_negi_i.
  rewrite addi_i_PO. reflexivity.
  Defined.

Lemma subi_addi : forall (i j : int), subi (addi i j) j = i.
  intros i j. rewrite subi_rel_addi.
  rewrite addi_assoc. rewrite addi_i_negi.
  rewrite addi_i_PO. reflexivity.
  Defined.

Lemma addi_subi_dist : forall (i j k l : int), addi (subi i j) (subi k l) = subi (addi i k) (addi j l).
  intros i j k l. rewrite ?subi_rel_addi. rewrite neg_addi.
  rewrite (addi_assoc i k (addi (neg j) (neg l))).
  rewrite <- (addi_assoc k (neg j) (neg l)).
  rewrite (addi_comm k (neg j)).
  rewrite (addi_assoc (neg j) k (neg l)).
  rewrite <- (addi_assoc i (neg j) (addi k (neg l))).
  reflexivity.
  Defined.

Fixpoint muli (i1 i2 : int) := 
  match i1, i2 with
  | P n1, P n2 => P (muln n1 n2)
  | P n1, N n2 => N (muln n1 n2)
  | N n1, P n2 => N (muln n1 n2)
  | N n1, N n2 => P (muln n1 n2)
  end.


Lemma muli_PO_j : forall (j : int), muli (P O) j = P O.
  destruct j; simpl; rewrite <- ?pz_equals_nz; reflexivity.
  Defined.

Lemma muli_i_PO : forall (i : int), muli i (P O) = P O.
  destruct i; simpl; rewrite ?muln_n_O; rewrite <- ?pz_equals_nz; reflexivity.
  Defined.

Lemma muli_PP : forall (n m : nat), muli (P n) (P m) = P (muln n m).
  reflexivity.
  Defined.

Lemma muli_PN : forall (n m : nat), muli (P n) (N m) = N (muln n m).
  reflexivity.
  Defined.

Lemma muli_NP : forall (n m : nat), muli (N n) (P m) = N (muln n m).
  reflexivity.
  Defined.

Lemma muli_NN : forall (n m : nat), muli (N n) (N m) = P (muln n m).
  reflexivity.
  Defined.

Theorem muli_comm : forall (i j : int), muli i j = muli j i.
  destruct i as [n|n]; destruct j as [m|m];
  rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN;
  rewrite muln_comm; reflexivity.
  Defined.

Theorem muli_assoc : forall (i j k : int), muli (muli i j) k = muli i (muli j k).
  destruct i as [n|n]; destruct j as [m|m]; destruct k as [o|o];
  try (rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN);
  try (rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN);
  rewrite muln_assoc; reflexivity.
  Defined.

Lemma muli_PSn_j : forall (n : nat) (j : int), muli (P (S n)) j = addi (muli (P n) j) j.
  intros n j.
  destruct j as [m|m];
  rewrite ?muli_PP; rewrite ?muli_PN;
  rewrite ?addiPP_eq_Paddn; rewrite ?addiNN_eq_Naddn;
  rewrite muln_Sn_m; rewrite addn_comm;
  reflexivity.
  Defined.

Lemma muli_NSn_j : forall (n : nat) (j : int), muli (N (S n)) j = subi (muli (N n) j) j.
  intros n j.
  destruct j as [m|m];
  rewrite ?muli_NP; rewrite ?muli_NN;
  rewrite subi_rel_addi; rewrite ?neg_Nn; rewrite ?neg_Pn;
  rewrite ?muln_Sn_m; rewrite ?addiNN_eq_Naddn; rewrite ?addiPP_eq_Paddn;
  rewrite addn_comm;
  reflexivity.
  Defined.

Lemma muli_i_PSm : forall (i : int) (m : nat), muli i (P (S m)) = addi (muli i (P m)) i.
  intros i m; rewrite (muli_comm i (P (S m)));
  rewrite muli_PSn_j. rewrite (muli_comm i (P m)).
  reflexivity.
  Defined.

Lemma muli_i_NSm : forall (i : int) (m : nat), muli i (N (S m)) = subi (muli i (N m)) i.
  intros i m. rewrite (muli_comm i (N (S m))).
  rewrite muli_NSn_j. rewrite (muli_comm i (N m)).
  reflexivity.
  Defined.

Lemma muli_inci_j : forall (i j : int), muli (inci i) j = addi (muli i j) j.
  destruct i as [n|n].
  (* i : P *)
    rewrite inci_Pn. intros j.  rewrite muli_PSn_j. reflexivity.
  (* i : N *)
    destruct n; rewrite <- ?pz_equals_nz; rewrite ?inci_NSn; rewrite ?inci_Pn;
    intros j.
      rewrite ?muli_PSn_j; reflexivity.
      rewrite ?muli_NSn_j. rewrite addi_subi. reflexivity.
  Defined.

Lemma muli_i_incj : forall (i j : int), muli i (inci j) = addi (muli i j) i.
  intros i j.
  rewrite muli_comm. rewrite muli_inci_j. 
  rewrite (muli_comm j i). reflexivity.
  Defined.

Lemma muli_deci_j : forall (i j : int), muli (deci i) j = subi (muli i j) j.
  destruct i as [n|n].
  (* i : P *)
    intros j.
    destruct n.
      rewrite -> ?pz_equals_nz; rewrite ?deci_Nn; rewrite ?muli_NSn_j; reflexivity.
      rewrite ?deci_PSn; rewrite muli_PSn_j; rewrite subi_addi; reflexivity.
  (* i : N *)
  rewrite ?deci_Nn. intros j. rewrite muli_NSn_j. reflexivity.
  Defined.

Lemma muli_i_decj : forall (i j : int), muli i (deci j) = subi (muli i j) i.
  intros i j.
  rewrite muli_comm. rewrite muli_deci_j.
  rewrite (muli_comm j i). reflexivity.
  Defined.

Lemma muli_negi_j : forall (i j : int), muli (neg i) j = neg (muli i j).
  destruct i as [n|n]; destruct j as [m|m];
  rewrite ?neg_Nn; rewrite ?neg_Pn;
  rewrite ?muli_PP; rewrite ?muli_NP; rewrite ?muli_PN; rewrite ?muli_NN;
  rewrite ?neg_Nn; rewrite ?neg_Pn;
  reflexivity.
  Defined.

Lemma muli_i_negj : forall (i j : int), muli i (neg j) = neg (muli i j).
  intros i j.
  rewrite muli_comm; rewrite muli_negi_j;
  rewrite muli_comm; reflexivity.
  Defined.

Lemma addi_subPPn : forall (n m o p : nat), addi (sub_PPn n m) (sub_PPn o p) = sub_PPn (addn n o) (addn m p).
  intros n m o p. rewrite <- ?subi_PP. rewrite <- ?addiPP_eq_Paddn. rewrite addi_subi_dist.
  reflexivity.
  Defined.

Lemma addi_subNNn : forall (n m o p : nat), addi (sub_NNn n m) (sub_NNn o p) = sub_NNn (addn n o) (addn m p).
  intros n m o p. rewrite <- ?subi_NN. rewrite <- ?addiNN_eq_Naddn. rewrite addi_subi_dist.
  reflexivity.
  Defined.

Lemma subPPn_muln : forall (n m o : nat), sub_PPn (muln n m) (muln n o) = muli (P n) (sub_PPn m o).
  induction n.
    (* n = 0 *) intros m o. rewrite ?muln_O_m. rewrite muli_PO_j. rewrite subPPn_n_O. reflexivity.
    (* n = S n' *) intros m o.
      rewrite muli_PSn_j. rewrite <- IHn. rewrite addi_subPPn.
      rewrite ?muln_Sn_m. rewrite (addn_comm m (muln n m)). rewrite (addn_comm o (muln n o)).
      reflexivity.
  Defined.

Lemma subNNn_muln : forall (n m o : nat), sub_NNn (muln n m) (muln n o) = muli (P n) (sub_NNn m o).
  induction n.
    (* n = O *) intros m o. rewrite ?muln_O_m. rewrite muli_PO_j. rewrite subNNn_n_O. rewrite pz_equals_nz. reflexivity.
    (* n = S n' *) intros m o.
      rewrite muli_PSn_j. rewrite <- IHn. rewrite addi_subNNn.
      rewrite ?muln_Sn_m. rewrite (addn_comm m (muln n m)). rewrite (addn_comm o (muln n o)).
      reflexivity.
  Defined.

Theorem muli_addi : forall (i j k : int), muli i (addi j k) = addi (muli i j) (muli i k).
  destruct i as [n|n]; destruct j as [m|m]; destruct k as [o|o];
  rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN;
  rewrite ?addiPP_eq_Paddn; rewrite ?addiNN_eq_Naddn;
  rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN;
  rewrite ?muln_addn_r; try reflexivity;
  rewrite ?addi_PN; rewrite ?addi_NP; rewrite ?subPPn_muln; rewrite ?subNNn_muln;
  try reflexivity; rewrite ?subPPn_neg_subNNn;
  rewrite ?muli_i_negj; rewrite <- ?neg_Pn; rewrite ?muli_negi_j;
  rewrite ?neg_neg; try reflexivity.
  Defined.

Theorem muli_subi : forall (i j k : int), muli i (subi j k) = subi (muli i j) (muli i k).
  intros i j k. rewrite ?subi_rel_addi. rewrite muli_addi.
  rewrite muli_i_negj. reflexivity.
  Defined.

(* integer absolute value *)
Fixpoint absi (i : int) :=
  match i with
  | P n => P n
  | N n => P n
  end.

Lemma absi_muli : forall (i j : int), absi (muli i j) = muli (absi i) (absi j).
  destruct i as [n|n]; destruct j as [m|m];
  rewrite ?muli_PP; rewrite ?muli_PN; rewrite ?muli_NP; rewrite ?muli_NN;
  unfold absi; rewrite muli_PP; reflexivity.
  Defined.

Lemma absi_N : forall (n : nat), absi (N n) = P n.
  reflexivity.
  Defined.

Lemma absi_P : forall (n : nat), absi (P n) = P n.
  reflexivity.
  Defined.

Lemma absi_neg : forall (i : int), absi (neg i) = absi i.
  destruct i as [n|n]; rewrite ?neg_Nn; rewrite ?neg_Pn;
  rewrite ?absi_N; rewrite ?absi_P;
  reflexivity.
  Defined.

(* naturals, subtraction, mod & integer division & euclid *)
(* divmod, div and modulo, subn from Coq init.nat *)

Fixpoint subn n m :=
  match n, m with
  | S k, S l => subn k l
  | _, _ => n
  end.

Fixpoint divmod x y q u :=
  match x with
    | O => (q,u)
    | S x' => match u with
                | O => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | O => y
    | S y' => fst (divmod x y' O y')
  end.

Definition modulo x y :=
  match y with
    | O => y
    | S y' => subn y' (snd (divmod x y' O y'))
  end.

Lemma divmod_O_y_q_u : forall (y q u : nat), divmod O y q u = (q, u).
  reflexivity.
  Defined.

Lemma divmod_Sx_y_q_O : forall (x y q : nat), divmod (S x) y q O = divmod x y (S q) y.
  reflexivity.
  Defined.

Lemma divmod_Sx_y_q_Su : forall (x y q u : nat), divmod (S x) y q (S u) = divmod x y q u.
  reflexivity.
  Defined.

Lemma divmod_fst_qadd : forall (x y q u : nat), fst (divmod x y q u) = addn (fst (divmod x y O u)) q.
  induction x.
  (* x = O *)
    rewrite ?divmod_O_y_q_u.
    unfold fst; rewrite ?addn_O_m; try reflexivity.
  (* x = S x' *)
    destruct u.
      (* u = O *)
        rewrite ?divmod_Sx_y_q_O.
        rewrite (IHx y (S q) y).
        rewrite (IHx y (S O) y).
        rewrite addn_assoc.
        rewrite addn_Sn_m; rewrite addn_O_m.
        reflexivity.
      (* u = S u' *)
        rewrite ?divmod_Sx_y_q_Su.
        rewrite (IHx y q u).
        reflexivity.
  Defined.

Lemma divmod_snd_qign : forall (x y q u : nat), snd (divmod x y q u) = snd (divmod x y O u).
  induction x.
  (* x = 0 *)
    intros y q u. rewrite ?divmod_O_y_q_u. reflexivity.
  (* x = S x' *)
    destruct u.
    (* u = O *)
        rewrite ?divmod_Sx_y_q_O.
        rewrite (IHx y (S q) y).
        rewrite (IHx y (S O) y).
        reflexivity.
    (* u = S u' *)
        rewrite ?divmod_Sx_y_q_Su.
        rewrite (IHx y q u).
        reflexivity.
  Defined.

Lemma divmod_x_O_q_O : forall (x q : nat), divmod x O q O = (addn x q, O).
  induction x; intros q.
  rewrite divmod_O_y_q_u. rewrite addn_O_m. reflexivity.
  rewrite divmod_Sx_y_q_O. rewrite addn_Sn_m. rewrite <- addn_n_Sm. rewrite IHx. reflexivity.
  Defined.





