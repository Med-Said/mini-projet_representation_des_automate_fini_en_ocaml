							(*besmi lahi rahmani rahum*)
(*l'automate est definit par ces deux type *)
type etat = {mutable num: int; mutable x: int; mutable y: int};;
type automate = {mutable q:etat list; mutable l:string list; mutable t:(etat*string*etat) list; mutable qi:etat; mutable f:etat list};;

let etat0 ={num=0; x=0; y=0};;
let auto0= {q = []; l = []; t = []; qi = {num = 0; x = 0; y = 0};f = []};;

open Graphics;;

(*les coleur des etats et labeles *)
let etats_color = rgb 135 206 235;;
let labeles_color = rgb 0 200 0;;

(*tous dabord on va definir toutes les fonctions necessaires(de base: complet les roles des autre fonctions) *)

(*DEBUT FONCTIONS NECESSAIRES*)

let first (x,y,z)=fst(x,y);;
let second (x,y,z)=fst(y,z);;
let last (x,y,z)=snd(y,z);;

let rec longueur l =
	match l with
	[] -> 0
	| hd::tl -> 1 + longueur tl
;;

let rec inverser l =
	match l with
	[] -> []
	| hd::tl -> (inverser tl)@[hd]
;;

let rec inser x l = match l with
	[] -> [x]
	| hd::tl -> if x < hd then x::hd::tl else hd::(inser x tl) 
;;

let rec tri_inser l k = match l with
	[] -> k
	| hd::tl -> tri_inser tl (inser hd k)
;;

let rec appartien element = function (*verifie la partenace d'un element dans une liste*)
  | [] -> false
  | hd::tl -> (element = hd) || (appartien element tl)
;;

let rec sup_double l =
	match l with
	[] -> []
	| hd::tl -> if appartien hd tl then sup_double tl else hd::(sup_double tl)
;;

let rec position x liste l(*l=liste*) =
	match liste with
	[] -> 0
	| hd::tl -> if x=hd  then  (longueur l)-(longueur tl) else position x tl l
;;

(*dans cette fonction deux transitons sont egales si ont le meme etat de depart et d'arrive aussi*)
let est_egal tran1 tran2 =
	((first tran1).num = (first tran2).num && (last tran1).num = (last tran2).num)
;;

(*sur les transitions chaque transiton et identifier par le numero d'etat de depart et l'etat d'arrive*)
let rec nombre_aparition x l =
	match l with
	[] -> 0
	| hd::tl -> if (est_egal x hd) then 1 + nombre_aparition x tl else nombre_aparition x tl
;;

(*ici la repetition est selon l'etat de depart et l'etat d'arrive (si sont meme ou non)*)
let rec tous_occurence x liste_transiton l(*l=liste_transition*) =
	match liste_transiton with
	[] -> []
	| hd::tl -> if  (est_egal x hd) && (nombre_aparition hd l) >1 then [hd]@(tous_occurence x tl l) else (tous_occurence x tl l)
;;

let rec liste_listes_non_repeter liste_transiton l =
	match liste_transiton with
	[] -> []
	| hd::tl -> if nombre_aparition hd l = 1 then [[hd]]@(liste_listes_non_repeter tl l) else liste_listes_non_repeter tl l
;;

(*lapliquatio de la fonciton tous_occurence.... sur une liste *)

(*apres avoire valider l'automate*)
(* fonction(s) renvoie(nt) les elements de la liste de transition sous la forme suvant : 
les element (transitions) ont meme etat de depart et d'arrive dans une liste separer(cette fonction donne une liste des listes)
*)
let rec liste_listes_repeter liste_transiton l(*L=liste_transiton*) =
	match liste_transiton with
	[] -> []
	| hd::tl ->  sup_double ([(tous_occurence hd l l)]@(liste_listes_repeter tl l))
;;

let draw_etat (x,y) =
	moveto 0 0;
	draw_circle x y 14
;;

(*debut divise liste en deux parties *)
let  premier_element_de_la_liste l = 
	match l with
	[] -> failwith "hd"
	| hd::_ -> hd
;;


let rec dernier_element_de_la_liste l =
	match l with
	[] -> failwith "dernier element"
	| hd::tl -> if tl =[] then hd else dernier_element_de_la_liste tl
;;

let list_sans_sa_premier_element l =
	match l with
	[] -> []
	| hd::tl -> tl
;;

let list_sans_ces_extrimite l =(*donne une liste vide s'elle contienne un seul element*)
	match l with
	[] -> []
	| hd::tl -> inverser (list_sans_sa_premier_element (inverser tl))
;;
let rec div_list l j k =(*etait la plus difficile a trover parmi toute les foncton jusqu'a ici*)
	match l with
	[] -> (inverser j,k)
	| [x] -> (inverser (x::j),k)
	| hd::tl as l -> let j2 = (premier_element_de_la_liste l)::j and k2 = (dernier_element_de_la_liste l)::k in div_list (list_sans_ces_extrimite l) j2 k2
;;(*fin divise liste un deux parti*)

(*FIN FONCTIONS NECESSAIRES*)

(*----------------------------------------------------------------------------------------------------------------------------------------------------------------------*)

(*1*)(*ensemble des fonctiones pour dessiner toutes les  transitions possibles*)

(*quatre fonctions dessinent les fleches des transitions*)

let draw_tete_line_dro (x,y)=
	draw_arc x y 7 3 270 90
;;

let draw_tete_line_gou (x,y) = 
	draw_arc x y 7 3 90 270
;;

let draw_tete_line_sup (x,y) = 
	draw_arc x y 3 7 0 180
;;

let draw_tete_line_inf (x,y) =
	draw_arc x y 3 7 180 0
;;

(*______________*)

(*les deux fonctons ci-dessous serent a 
dessiner les different cas possible d'une
 transition d'une etat vers lui meme*)

let draw_trans_vers_meme_etat_sup (x,y) =
	draw_circle x y 14;
	draw_arc x y 14 40 30 114;
	draw_tete_line_inf ((x-10),(y+27))
;;

(*la seul difference entre les dexu fonction ...._sup 
et ...._inf est une simple modification de l'angle*)

let draw_trans_vers_meme_etat_inf (x,y) =
	draw_circle x y 14;
	draw_arc x y 14 40 210 294;
	draw_tete_line_sup ((x+10),(y-27))
;;

(*_______________*)

(*les quatre transition possible entre deux etat
 ont separe par une etat ou plus*)

let draw_trans_horz_sup (x,y) (m,n) =
	moveto 0 0;
	draw_etat (x,y);  draw_etat (m,n) ;
	moveto (x+21) (y+7);
	lineto (m-21) (n+7);
	draw_tete_line_dro ((m-21),(n+7))
;;

let draw_trans_horz_inf (x,y) (m,n) =
	moveto 0 0;
	draw_etat (x,y);  draw_etat (m,n) ;
	moveto (x+21) (y-7);
	lineto (m-21) (n-7);
	draw_tete_line_gou ((x+21),(y-7))
;;

let draw_trans_vert_dro (x,y) (m,n) =
	moveto 0 0;
	draw_etat (x,y);  draw_etat (m,n) ;
	moveto (x+7) (y-21);
	lineto (m+7) (n+21);
	draw_tete_line_sup ((x+7),(y-21))
;;

let draw_trans_vert_gou (x,y) (m,n) =
	moveto 0 0;
	draw_etat (x,y);  draw_etat (m,n) ;
	moveto (x-7) (y-21);
	lineto (m-7) (n+21);
	draw_tete_line_inf (((m-7),(n+21)))
;;

(*_________________*)

(*ces deux fonctioins dessent les transitons entre deux etats ont  separe au moins par une autre etat*)

(*m,n  sont les coordonnees du centre de l'etat situe a droite
ou en bas  parraport a l'etat de coordonnees x,y*)

let draw_arc_sup_dro (x,y) (m,n) =
	moveto (x+3) (y+20);
	curveto (x+3,y+20) ((x+m)/2,y+30*(m-x)/150) (m-7,n+20);
	draw_tete_line_inf ((m-7),(n+23));
	moveto 0 0
;;

let draw_arc_inf_gou (x,y) (m,n) =
	moveto (x-3) (y-20);
	curveto (x-3,y-20) ((x+m)/2,y-30*(x-m)/150) (m+3,n-20);
	draw_tete_line_sup ((m+3),(n-23));
	moveto 0 0
;;

(*______________*)

(*les transitions de la forme diagonaliste:
 entre deux etat n'on pas la meme ligne ni
  la meme colone*)
  
let draw_trans_diag_dro_d (x,y) (m,n) =
  moveto 0 0;
  moveto (x+28) (y-14);
  lineto (m-14) (n+28);
  draw_tete_line_gou ((x+28),(y-14))
;;

let draw_trans_diag_gou_d (x,y) (m,n) =
  moveto 0 0;
  moveto (x+14) (y-28);
  lineto (m-28) (n+14);
  draw_tete_line_dro ((m-28),(n+14))
;;

let draw_trans_diag_dro_g (x,y) (m,n) =
  moveto 0 0;
  moveto (x-28) (y-14);
  lineto (m+14) (n+28);
  draw_tete_line_dro((x-28),(y-14))
;;

let draw_trans_diag_gou_g (x,y) (m,n) =
  moveto 0 0;
  moveto (x-14) (y-28);
  lineto (m+28) (n+14);
  draw_tete_line_gou ((m+28),(n+14))
;;

(*----------------------------------------------------------------------------------------------------------------*)

(*2*)(*ensemble de fonctions pour dessiner les different type d'etats possibles ....*)
(*BLOC A: dessine toutes les etats : *)
(*DEBUT BLOC A*)
let draw_etat (x,y) =
	moveto 0 0;
	draw_circle x y 14
;;

(*____________*)

let rec position_etat_sup n (x,y) =
	moveto 0 0 ;
	draw_etat (x,y);
	moveto x y;
	if (n>1) then
	begin
		position_etat_sup (n-1) ((x+150),y);
	end
else
	moveto x y
;;

(*__________*)

let rec position_etat_inf n (x,y) =
	moveto 0 0;
	draw_etat (x,y);
	moveto x y;
	if (n>1) then
	begin
		position_etat_inf (n-1) ((x-150),y)
	end
else
	moveto x y
;;

(*___________*)

let position_etats n = 
	if (n=1) then
	draw_etat (150,600)
else
	if (n>0 && (n mod 2) = 0) then
	begin
		position_etat_sup ((n/2)) (150,600);
		let (cx,cy) = current_point() in
		position_etat_inf ((n/2)) (cx,(cy-150))
	end
else 
	if (n>0 && (n mod 2) <> 0) then
	begin
		position_etat_sup ((n/2)+1) (150,600);
		let (cx,cy) = current_point() in
		position_etat_inf ((n/2)) (cx,(cy-150))
	end
else
	moveto 0 0;
;;

(*________________*)

(*pour dessiner les numeros des etats(1,2...7..)*)
let draw_etat_num eta =
	set_color etats_color;
	moveto (eta.x-4) (eta.y-6);
	let c = string_of_int eta.num in
	draw_string c;
	moveto 0 0;
	set_color black
;;

(*________________*)

let rec draw_all_etats_num list_etats =
	match list_etats with
	[] -> moveto 0 0
	| hd::tl -> draw_etat_num hd; draw_all_etats_num tl
;;

(*FIN BLOC A*)

(*BLOC B: uniquement pour l'etat initial*)
(*DEBUT BLOC B*)

(*draw_etat_initial: fonction dessine l'etat initial*)
let draw_etat_init (x,y) =
	moveto 0 0;
	moveto x y;
	moveto (x-100) y;
	set_color blue;
	lineto (x-30) y;
	draw_tete_line_dro (x-30,y);
	set_color black;
	draw_circle x y 14
;;

(*_______________*)

let draw_etat_initial_global eta list_etats= (*x de type etat= automate.qi *)
	let x = eta.x and y = eta.y in
	if ((x,y) = (150,600) || (x,y) = (150,450) && ((longueur list_etats) mod 2 = 0) || (x,y) = (300,450) && ((longueur list_etats) mod 2 <> 0)) then
	draw_etat_init (x,y)
else (*dans le if corespondant a cette else on combine plusieur fonctionS predefini dans le programme a fin de recuperer les coordonnees de la dernier etat de la premier ligne ou ...*)
	if ((x,y) = ((dernier_element_de_la_liste (fst (div_list list_etats [] [] (*automate.q*)))).x,(dernier_element_de_la_liste (fst (div_list list_etats [] [] (*automate.q*)))).y)
|| (x,y) = ((premier_element_de_la_liste (snd (div_list list_etats [] [] (*automate.q*)))).x,(premier_element_de_la_liste (snd (div_list list_etats [] [] (*automate.q*)))).y)) then
	begin
		set_color blue;
		moveto (x+21) y;
		lineto (x+21+30) y;
		draw_tete_line_gou (x+21+3,y);
		set_color black
	end
else
	(*if y = 450 then
	begin
		set_color blue;
		moveto x (450-21);
		lineto x (450-21-30);
		draw_tete_line_sup (x,450-21-3);
		set_color black
	end
else
	if y=600 then*)
	begin
		set_color blue;
		moveto (x+14) (y+14); 
		lineto (x+17+7) (y+17+7);
		moveto (x+14) (y+14);
		lineto (x+14) (y+14+3);
		moveto (x+14) (y+14);
		lineto (x+14+3) (y+14);
		set_color black
	end
;;

(*_________________*)

(*FIN BLOC B*)

(*BLOC C : tous pour etats finaux*)
(*DEBUT BLOC C*)

(*ici on donne la fonction avec  un seul argumment ,
donc ona besoin ensuite d'une autre fonction  appliquera cette fonction 
sur le reste de la liste de etats finaux*)

let draw_etat_fin (x,y) =
	set_color red;
	draw_circle x y 17;
	set_color black
;;

(*____________*)

let rec draw_all_etats_fin liste_etats_finaux list_etats  =
	match liste_etats_finaux with
	[] -> moveto 0 0
	| hd::tl -> if (appartien hd list_etats) then
				begin
					draw_etat_fin (hd.x,hd.y);
					draw_all_etats_fin tl list_etats
				end
			else
			draw_all_etats_fin tl list_etats
		;;

(*FIN BLOC C*)

(*-------------------------------------------------------------------------------------------------------------------*)
(*3*)(*ensemble de fonctions dessinent les transitions existent*)

(*BLOC D: associer des coordonnees a les etats existent*)
(*DEBUT BLOC D*)

(*ajouter_x_y: fonciton qui associe deux coordonnees a chaque etat de liste q*)

let rec ajouter_x_y_sup l taill n(*n=1*) = 
	match l with
	[] -> moveto 0 0
	| hd::tl -> if (1<= taill && n <= taill) then 
				begin
					hd.num <- n;
					hd.x <- hd.x + 150*n;
					hd.y <- 600;
					ajouter_x_y_sup tl taill (n+1)
				end
			else moveto 0 0
			;;

 let aj = ajouter_x_y_sup;;

 (*fin ajouter_x_y_sup*)

 let rec ajouter_x_y_inf l  n cx(*=0*) = (*n: num, doit etre =  n + 1(de la fonction ajou...sup)*)
	match l with
	[] -> moveto 0 0
	| hd::tl -> if (150 <= cx) then
				begin
					hd.num <- n;
					hd.x <- cx ;(*cx: current_point_x en ce basant sur la fonction ajou...sup*)
					hd.y <- 450;
					let cx = cx -150 in
					ajouter_x_y_inf tl  (n+1)  cx
				end
			else moveto 0 0
			;;
let aji = ajouter_x_y_inf;;

let associer_cor l =(*l: est la liste des etats*)
	let (j,k) = div_list l [] [] in
	ajouter_x_y_sup j (longueur j) 1;

	let cx = (dernier_element_de_la_liste j).x in

	let n = (longueur j ) + 1 in
	ajouter_x_y_inf k n cx 
;;

(*FIN BLOC D*)

(*pour dessiner les labels (les symboles de la langage de l'automate*)
let draw_label lab x y = 
	moveto x y;
	set_color labeles_color;
	draw_string lab;
	set_color black
;;

(*______________*)

let rec draw_label_liste liste(*liste des transition, liste=l*) l  =(*toustes les transitions de cette liste ont les meme etats de depart et d'arrive*)
	match liste with
	[] -> moveto 0 0
	| tran::tl -> 
	 let x = (first tran).x and y = (first tran).y and m = (last tran).x and n = (last tran).y and label = (second tran) in
			if ( ((first tran).num = (last tran).num) && y=600 ) then
				begin
					draw_trans_vers_meme_etat_sup (x,y);
					draw_label label (x+14-(position tran liste l)*14) (y+14);
					draw_label_liste tl l
 
				end
			else
				if ( ((first tran).num = (last tran).num) && y=450 ) then
				begin
					draw_trans_vers_meme_etat_inf (x,y);
					draw_label label (x-21+(position tran liste l)*14) (y-21);
					draw_label_liste tl l 
				end
			else
				if (m-x=150 && y=n) then
				begin
					draw_trans_horz_sup (x,y) (m,n);
					draw_label label ((x+m)/2-24+(position tran liste l)*14) (y+14);
					draw_label_liste tl l
				end
			else
				if (x-m=150 && y=n) then
				begin
					draw_trans_horz_inf (m,n) (x,y);
					draw_label label ((x+m)/2+30-(position tran liste l)*14) (y-21);
					draw_label_liste tl l
				end
			else
				if (x=m && y<n) then
				begin
					draw_trans_vert_dro (m,n) (x,y);
					draw_label label (x+10) ((y+n)/2-30+(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				if (x=m && n<y) then
				begin
					draw_trans_vert_gou (x,y) (m,n);
					draw_label label (x-17) ((y+n)/2+30-(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				if (m-x>150 && y=n) then
				begin
					if (m-x = 300) then
					begin
						draw_arc_sup_dro (x,y) (m,n);
						draw_label label ((x+m)/2-30+(position tran liste l)*14) (y+30*(m-x)/150-24);
						draw_label_liste tl l
					end
				else
					begin
						draw_arc_sup_dro (x,y) (m,n);
						draw_label label ((x+m)/2-30+(position tran liste l)*14) (y+21*(m-x)/150-17);
						draw_label_liste tl l
					end
				end
			else
				if (x-m>150 && y=n) then
				begin
					if ((x-m)=300) then
					begin
						draw_arc_inf_gou (x,y) (m,n);
						draw_label label ((m+x)/2-(position tran liste l)*14) (y-30*(x-m)/150+14);
						draw_label_liste tl l
					end
				else
					begin
						draw_arc_inf_gou (x,y) (m,n);
						draw_label label ((m+x)/2-(position tran liste l)*14) (y-21*(x-m)/150);
						draw_label_liste tl l
					end
				end
			else
				if (x<m && y<n) then
				begin
					draw_trans_diag_dro_g (m,n) (x,y);
					(*3*)draw_label label ((x+m)/2-30+(position tran liste l)*14) ((y+n)/2-10+(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				if (m<x && n<y) then
				begin
					draw_trans_diag_gou_g (x,y) (m,n);
					(*4*)draw_label label ((x+m)/2+33-(position tran liste l)*14) ((y+n)/2+10-(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				if (x<m && y>n) then
				begin
					draw_trans_diag_gou_d (x,y) (m,n);
					(*2*)draw_label label ((x+m)/2-40+(position tran liste l)*14) ((y+n)/2+10-(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				if (x>m && y<n) then
				begin
					draw_trans_diag_dro_d (m,n) (x,y);
					(*1*)draw_label label ((x+m)/2+30-(position tran liste l)*14) ((y+n)/2-17+(position tran liste l)*14);
					draw_label_liste tl l
				end
			else
				moveto 0 0
				;;

let rec draw_label_liste_listes liste_transiton = (*resultat des fonctions liste_listes_repeter @ liste_listes_non_repeter de la liste des vrai transitions(transitions de l'automate avant tous modification)*)
	match liste_transiton with
	[] -> moveto 0 0
	| hd::tl -> draw_label_liste hd hd; draw_label_liste_listes tl
;;

(*********************************************************************************************************************************)
(*********************************************************************************************************************************)
(*********************************************************************************************************************************)

let mise_etats_en_place auto =
	position_etats (longueur auto.q);
	(*associer_cor auto.q;*)
	draw_etat_initial_global auto.qi auto.q;
	draw_all_etats_fin auto.f auto.q;
	draw_all_etats_num auto.q
;;

let mise_transitions_en_place auto =
	draw_label_liste_listes ((liste_listes_non_repeter auto.t auto.t)@(liste_listes_repeter auto.t auto.t))
;;
let dessiner_automate auto =
	mise_etats_en_place auto;
	mise_transitions_en_place auto;

;;

(*sup_double_et_tri_automate*)

let sup_double_et_tri_automate auto =
	auto.q<-sup_double auto.q;
	auto.l<-sup_double auto.l;
	auto.t<-sup_double auto.t;
	auto.f<-sup_double auto.f;
	auto.q<-tri_inser auto.q [];
	auto.l<-tri_inser auto.l [];
	auto.t<-tri_inser auto.t [];
	auto.f<-tri_inser auto.f [];
	auto
;;

(*quelque modification avant dessiner ex: lier les etats et les transitons,..*)


(*ces  fonctions permetent de recuperer les etats de la liste de etats apartire de leur numero saisie par l'utilisateur lors de la remplisage de la liste des transiton*)

let rec aide_f liste_etats (etat_d,label,etat_a) =
	match liste_etats with
	[] -> (etat0,label,etat0)
	| hd::tl -> if (hd.num)=(etat_d.num) then (hd,label,etat_a)
				else aide_f tl (etat_d,label,etat_a)
			;;

(*aide_f et aide_g completent la fonction recuper_etat_aprtire_de_num*)

let rec aide_g liste_etats (etat_d,label,etat_a) =
	match liste_etats with
	[] -> (etat0,label,etat0)
	| hd::tl -> if (hd.num)=(etat_a.num) then  (etat_d,label,hd)
				else aide_g tl (etat_d,label,etat_a)
			;;

let rec recuper_etat_apartire_de_num liste_etats (etat_d,label,etat_a) =
	match liste_etats with
	[] -> (etat0,label,etat0)
	| hd::tl -> if (hd.num)=(etat_d.num) && (hd.num)=(etat_a.num) then (hd,label,hd)
			else 
				if (hd.num)=(etat_d.num) then aide_g liste_etats (hd,label,etat_a)
			else
				if (hd.num)=(etat_a.num) then  aide_f liste_etats (etat_d,label,hd)
			else
				recuper_etat_apartire_de_num tl (etat_d,label,etat_a)
		;;

(*cette fonciton donne les coordonnees des etats a les etats dans la liste de transiton
elle donne une novelle liste des transition pres a utiliser
*)
let rec lier_les_etats_et_les_transiton liste_etats liste_transitions =
	match liste_transitions with
	[] -> []
	| hd::tl -> [(recuper_etat_apartire_de_num liste_etats hd)]@(lier_les_etats_et_les_transiton liste_etats tl)
;;

let rec recuper_etat_apartire_de_num2 liste_etats etat =
	match liste_etats with
	[] -> etat0
	| hd::tl -> if hd.num = etat.num then hd
			else recuper_etat_apartire_de_num2 tl etat
		;;

let rec lier_les_etats_et_les_etat_finaux liste_etats liste_etats_finaux =
	match liste_etats_finaux with
	[] -> []
	| hd::tl -> [recuper_etat_apartire_de_num2 liste_etats hd]@(lier_les_etats_et_les_etat_finaux liste_etats tl)
;;

let rec lier_les_etats_et_etat_initial liste_etats etat_initial =
	match liste_etats with
	[] -> etat0
	| hd::tl -> if hd.num = etat_initial.num then hd else lier_les_etats_et_etat_initial tl etat_initial
;;

let lier_globale auto =
	associer_cor auto.q;
	auto.t <- lier_les_etats_et_les_transiton auto.q auto.t;
	auto.f <- lier_les_etats_et_les_etat_finaux auto.q auto.f;
	auto.qi <- lier_les_etats_et_etat_initial auto.q auto.qi;
	open_graph "1400x1400";
	auto
;;

(*lire automate*)

let rec lire_liste_etat taill l=
	match taill with
	0 -> l
	| _ -> lire_liste_etat (taill-1) ({etat0 with num=read_int()}::l)
;;

let rec lire_liste_string taill l =
	match taill with
	0 -> l
	| _ -> lire_liste_string (taill-1) ((read_line())::l)
;;

let lire_transition() =
	let () = print_string "etat de depart (ex: 1) : " in
	let x = {etat0 with num = read_int() } in
	let () = print_string "label (ex: a) : " in
	let y = read_line () in
	let () = print_string "etat d'arrive (ex: 2): " in
	let z = {etat0 with num=read_int()} in
	(x,y,z)
;;
         
let rec lire_liste_transiton taill l =
	match taill with
	0 -> l
	| _ -> lire_liste_transiton (taill-1) ((lire_transition())::l)
;;

let lire_automate  auto =
	let () = print_string "saisissez le nombre des etats de l'automate (pas les etats eux meme !!!) : " in
	let taillq = read_int() in
	let () = print_string "saisissez les etats de l'automate (entiers 1,2...) : " in
	auto.q <- inverser (lire_liste_etat taillq []);
	let () = print_string "saisissez l'etat initial de l'automate (entier 1 ou 2 ou ...): " in
	(auto.qi).num <- read_int();
	let () = print_string "saisissez le nombre des etats finaux de l'automate (pas les etats eux meme !!!) : " in
	let taillf = read_int() in
	let () = print_string "saisissez les etats finaux de l'automate: " in
	auto.f <- inverser (lire_liste_etat taillf []);
	let () = print_string "saisissez le nombre des lettres de l'aphabet de l'automate (pas les lettres eux meme !!!): " in
	let tailll = read_int() in
	let () = print_string "saisissez les lettres de l'aphabet de l'automate (a, b, ...): " in
	auto.l <- inverser (lire_liste_string tailll []);
	let () = print_string "saisissez le nombre des transitions de l'automate (pas les transitions eux meme !!!): " in
	let taillt = read_int() in
	auto.t <- inverser (lire_liste_transiton taillt []);
	auto
;;

(*valider & dessiner*)

(*description: la fonction valider_global prend comme parametre une automate et revoi l'automate pris s'elle est valide 
(une automate est valide s'elle est une automate ,l'etat initial appartien de la liste des etat et les etats
finaux aussi et que les etat et les lettre des transitions soient respectivement dans la liste des etat et la 
liste des lettre de l'alphabet de l'automate)si non elle renvoi un message d'erreur
donc on a besoin des fonctions verifient si une liste est contenu dans une autre liste ,une fonction appartien
verifie si un l'etat initial est contenu dans la liste d'etat et une dernier fonction (ou ensemble des fonctions) qui va verifier 
a la fois si chaque deux etat et la label correspondant de la liste des transition sont respectivement contenu
dans la liste d'etats et la liste des lettre de l'lphabet de l'automate*)
let valider_global auto =
	let rec appartien element = function (*verifie la partenace d'un element dans une liste*)
  		| [] -> false
  		| hd::tl -> (element = hd) || (appartien element tl)
in(*les deux liste sont supposes non vide *)
	let rec appartien_liste liste_contien liste_est_contenu =
		match liste_est_contenu with
		[] -> true 
		| hd::tl -> (appartien hd liste_contien) && (appartien_liste liste_contien tl)
in(*une fonction valide la liste des transitons ,est explique dans la commentaire de description*)
	(*toutes les listes sont supposees non vide*)(*les cas des listes vides sont eliminer avant arriver a ici*)
let rec valider_liste_transitions liste_etats liste_lettres liste_transitions =
	let first (x,y,z)=fst(x,y) and second (x,y,z)=fst(y,z) and last (x,y,z)=snd(y,z) in
	match liste_transitions with
	[] -> true
	| hd::tl -> (appartien (first hd) liste_etats) && (appartien (last hd) liste_etats) && (appartien (second hd) liste_lettres)
				&& valider_liste_transitions liste_etats liste_lettres tl
in
	(appartien auto.qi auto.q) && (appartien_liste auto.q auto.f) && (valider_liste_transitions auto.q auto.l auto.t)
;;

let valider_automate auto =
	let detect_liste_vide l =(*elle renvoi true si la liste est vide sinon elle renvoi false*)
	match l with
	[] -> true
	| _::_ -> false
in
	if (detect_liste_vide auto.q) || (detect_liste_vide auto.l) || (detect_liste_vide auto.q) || (detect_liste_vide auto.f) then
	failwith "!!!n'est pas automate"
else
	if not (valider_global auto) then
	failwith "!!!erreur verifier votre automate "
else (*le cas ou l'automate est valide*)
	auto
;;
dessiner_automate (lier_globale (sup_double_et_tri_automate (valider_automate (lire_automate auto0))));;
read_line();;