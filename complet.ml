(*le type automate defini l'ensemble des automates*)
  type automate = {mutable q:int list; mutable l:string list; mutable t:(int*string*int) list; mutable qi:int; mutable f:int list};;

(*description de la type automate; q: liste des etats , l: l'aphabet , t: les transitions,
qi: l'etat initial et f: les etats finaux*)
(*l'idee : si le nombre des transitions est egale a la produt entre les etats et les lettres
de l'alphabet de l'automate alors l'automate est complet
deroulement apres avoire supprimer tous les repetition pas plus de verifier cette egalite*)
let auto0= {q = []; l = []; t = []; qi = 0; f = []};;

let rec lire_liste taill l(*l=[]*) =
	match taill with
	0 -> l
	| _ -> (read_int())::(lire_liste (taill-1) l)
;;

let rec lire_liste_string taill l =
	match taill with
	0 -> l
	| _ -> lire_liste_string (taill-1) ((read_line())::l)
;;

let lire_transition() =
	let () = print_string "etat de depart (ex: 1) : " in
	let x = read_int() in
	let () = print_string "label (ex: a) : " in
	let y = read_line () in
	let () = print_string "etat d'arrive (ex: 2): " in
	let z = read_int() in
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
	auto.q <- (lire_liste taillq []);
	let () = print_string "saisissez l'etat initial de l'automate (entier 1 ou 2 ou ...): " in
	auto.qi <- read_int();
	let () = print_string "saisissez le nombre des etats finaux de l'automate (pas les etats eux meme !!!) : " in
	let taillf = read_int() in
	let () = print_string "saisissez les etats finaux de l'automate: " in
	auto.f <- (lire_liste taillf []);
	let () = print_string "saisissez le nombre des lettres de l'aphabet de l'automate (pas les lettres eux meme !!!): " in
	let tailll = read_int() in
	let () = print_string "saisissez les lettres de l'aphabet de l'automate (a, b, ...): " in
	auto.l <- (lire_liste_string tailll []);
	let () = print_string "saisissez le nombre des transitions de l'automate (pas les transitions eux meme !!!): " in
	let taillt = read_int() in
	auto.t <- lire_liste_transiton taillt [];
	auto
;;

(*sup_double_et_tri_automate est une fonction que supprime et tri tous les liste d'un automate*)

let sup_double_et_tri_automate auto =

	let rec appartien element = function (*verifie la partenance d'un element dans une liste*)
  		| [] -> false
  		| [x] -> if x=element then true else false
  		| hd::tl -> (element = hd) || (appartien element tl)
in(*la fonction sup_double : supprime tous les repetitions dans une liste*)
	let rec sup_double l =
		match l with
		[] -> []
		| hd::tl -> if appartien hd tl then sup_double tl else hd::(sup_double tl)
in(*la fonction inser : insere un element dans une liste juste avant le premier element plus grand que lui*)
	let rec inser x l = match l with
		[] -> [x]
		| hd::tl -> if x < hd then x::hd::tl else hd::(inser x tl) 
in(*la fonction tri_inser utilise la fonction inser pour trier une liste*)
	let rec tri_inser l k = match l with
		[] -> k
		| hd::tl -> tri_inser tl (inser hd k)
in
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

let complet auto=
(*la fonction longuer retourne la longuer d'une liste *)
  let rec longueur l =
  match l with 
  [] -> 0
  |_::tl -> 1+longueur tl

 in(*cet expressin peut determine si une automate est complet ou non *)  
 	((longueur auto.t) = ((longueur auto.l) * (longueur auto.q)))
in 
	if complet (sup_double_et_tri_automate (valider_automate (lire_automate auto0))) then 
	print_string "\ntrue\n"
else
	print_string "\nfalse\n"
;;