
Theorem a : 4 <> 1.
Proof.
    discriminate.
    Show Proof.
Qed.

Definition b (e : 4 = 2) : False :=
    match e 
    in _ = j 
    return 
        match j with 
        | 4 => True
        | _ => False
        end 
    with 
    | eq_refl => I
    end. 

Theorem c: forall A B, A -> A = B -> B.
Proof.
    intros A B a ->.
    exact a.
Qed.



Print eq_ind.

Definition c (e : 4 = 2) : False :=
    eq_ind 4 (fun p => match p with
                       | 4 => True 
                       | _ => False 
                       end) I 2 e.