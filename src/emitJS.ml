open CoreAst
open TypedAst
open TypedAstPrinter
open Assoc
open Lin_ops
open Util

let comp_type (t : etyp) : string =
    match t with
    | UnitTyp -> "void"
    | BoolTyp -> "boolean"
    | IntTyp -> "number"
    | FloatTyp -> "number"
    | VecTyp n -> "vec" ^ (string_of_int n)
    | MatTyp (m, n) -> "mat" ^ (string_of_int (max m n))
    | TransTyp _ -> failwith "Cannot represent TransTyp in Javascript"
    | SamplerTyp n -> failwith "Cannot represent SamplerTyp in Javascript"
    | SamplerCubeTyp -> failwith "Cannot represent SamplerCubeTyp in Javascript"
    | AbsTyp _ -> failwith "Cannot represent AbsTyp in Javascript"

let rec comp_value (v : value) : string =
    match v with
    | Unit -> "null"
    | Bool b -> "<boolean>" ^ string_of_bool b
    | Num n -> "<number>" ^ string_of_int n
    | Float f -> string_of_float f
    | VecLit v -> "[" ^ (String.concat "," (List.map string_of_float v)) ^ "]"
    | MatLit m -> String.concat "," (List.map (fun v -> String.concat "," (List.map string_of_float v)) m)


let rec comp_exp (e : exp) : string =
    match e with
    | Val v -> comp_value v
    | Var x -> x
    | Arr el -> "[" ^ (String.concat "," (List.map (fun (e, _) -> comp_exp e) el)) ^ "]"
    | Unop (op, (e, t)) ->
        begin
            match t with
            | VecTyp n ->
                begin
                    match op with
                    | Neg -> "vec" ^ (string_of_int n) ^ "negate.(__vec" ^ (string_of_int n) ^ "," ^ (comp_exp e) ^ ");"
                    | _ -> failwith "Cannot apply this operator to vector"
                end
            | MatTyp (m, n) ->
                begin
                    match op with
                    | Neg -> "mat" ^ (string_of_int (max m n)) ^ "negate.(__mat" ^ (string_of_int (max m n)) ^ "," ^ (comp_exp e) ^ ");"
                    | _ -> failwith "Cannot apply this operator to matrix"
                end
            | _ -> string_of_unop op (comp_exp e)
        end
    | Binop (op, (e1, t1), (e2, t2)) ->
        begin
            match t1, t2 with
            | VecTyp n, VecTyp _ ->
                let typ_string = "vec" ^ (string_of_int n) in
                let op_string =
                    match op with
                    | Eq -> "equals"
                    | Plus -> "add"
                    | Minus -> "sub"
                    | Div -> "div"
                    | CTimes  -> "mul"
                    | _ -> failwith "Cannot apply " ^ (binop_string op) ^ "to vectors"
                in
                typ_string ^ "." ^ op_string ^ "(__" ^ typ_string ^ "," ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
            | VecTyp n, IntTyp | VecTyp n, FloatTyp ->
                let typ_string = "vec" ^ (string_of_int n) in
                typ_string ^ ".scale(__" ^ typ_string ^ "," ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
            | IntTyp, VecTyp n | FloatTyp, VecTyp n ->
                let typ_string = "vec" ^ (string_of_int n) in
                typ_string ^ ".scale(__" ^ typ_string ^ "," ^ (comp_exp e2) ^ "," ^ (comp_exp e1) ^ ")"
            | VecTyp n, MatTyp _ ->
                let typ_string = "vec" ^ (string_of_int n) in
                typ_string ^ ".transformMat" ^ (string_of_int n) ^ "(__" ^ typ_string ^ "," ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
            | MatTyp _, VecTyp n ->
                let typ_string = "vec" ^ (string_of_int n) in
                typ_string ^ ".transformMat" ^ (string_of_int n) ^ "(__" ^ typ_string ^ "," ^ (comp_exp e2) ^ "," ^ (comp_exp e1) ^ ")"
            | MatTyp (m, n), MatTyp _ ->
                let typ_string = "mat" ^ (string_of_int (max m n)) in
                typ_string ^ ".mul" ^ "(__" ^ typ_string ^ "," ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
            | _ -> string_of_binop op (comp_exp e1) (comp_exp e2)
        end
    | FnInv (f, args) -> f ^ "(" ^ (String.concat "," (List.map comp_exp args)) ^ ")"

let comp_assign_mat_vec (x : id) (e : exp) (typ_str : string) (n : int) : string =
    let func, args = match e with
        | Val v -> "set", comp_value v
        | Var _ | FnInv _ -> "copy", comp_exp e
        | Arr el ->
            let rec comp_args el = match el with
                | (e, FloatTyp)::tl | (e, IntTyp)::tl -> (comp_exp e)::(comp_args tl)
                | (Arr el, VecTyp _)::tl -> (List.map (fun (e,t) -> comp_exp e) el)@(comp_args tl)
                | _ -> []
            in "set", String.concat "," (comp_args el)
        | Unop (op, (e, t)) ->
            begin
                match op with
                | Neg -> "negate", comp_exp e
                | _ -> failwith "Cannot apply this operator to create vector or matrix"
            end
        | Binop (op, (e1, t1), (e2, t2)) ->
            match op with
            | Plus -> "add", (comp_exp e1) ^ "," ^ (comp_exp e2)
            | Minus -> "sub", (comp_exp e1) ^ "," ^ (comp_exp e2)
            | Div -> "div", (comp_exp e1) ^ "," ^ (comp_exp e2)
            | CTimes ->
                begin
                    match t1, t2 with
                    | VecTyp _, VecTyp _ -> "mul", (comp_exp e1) ^ "," ^ (comp_exp e2)
                    | _ -> failwith "component-wise multiplication can only be applied to vectors"
                end
            | Times ->
                begin
                    match t1, t2 with
                    | VecTyp _, IntTyp | VecTyp _, FloatTyp -> "scale", (comp_exp e1) ^ "," ^ (comp_exp e2)
                    | IntTyp, VecTyp _ | FloatTyp, VecTyp _ -> "scale", (comp_exp e2) ^ "," ^ (comp_exp e1)
                    | MatTyp _, IntTyp | MatTyp _, FloatTyp -> "multiplyScalar", (comp_exp e1) ^ "," ^ (comp_exp e2)
                    | IntTyp, MatTyp _ | FloatTyp, MatTyp _ -> "multiplyScalar", (comp_exp e2) ^ "," ^ (comp_exp e1)
                    | VecTyp _, MatTyp _ -> "transformMat" ^ (string_of_int n), (comp_exp e1) ^ "," ^ (comp_exp e2)
                    | MatTyp _, VecTyp _ -> "transformMat" ^ (string_of_int n), (comp_exp e2) ^ "," ^ (comp_exp e1)
                    | MatTyp _, MatTyp _ -> "mul", (comp_exp e1) ^ "," ^ (comp_exp e2)
                    | _ -> failwith ("cannot multiply " ^ string_of_typ t1 ^ " by " ^ string_of_typ t2 ^ " to produce vector or matrix")
                end
            | Eq | Leq | Lt | Geq | Gt | Or | And | Index -> failwith ((binop_string op) ^ " cannot result in vector or matrix")
    in
    typ_str ^ (string_of_int n) ^ "." ^ func ^ "(" ^ x ^ "," ^ args ^ ");"

let comp_assign (x : id) ((e, t) : texp) : string =
    match t with
    | UnitTyp | BoolTyp | IntTyp | FloatTyp -> x ^ "=" ^ (comp_exp e) ^ ";"
    | VecTyp v -> comp_assign_mat_vec x e "vec" v
    | MatTyp (m, n) -> comp_assign_mat_vec x e "mat" (max m n)
    | TransTyp _ | SamplerTyp _ | SamplerCubeTyp | AbsTyp _ -> comp_type t

let rec comp_comm_lst (cl : comm list) : string =
    debug_print ">> comp_comm_lst";
    match cl with
    | [] -> ""
    | h::tl -> match h with
        | Skip -> comp_comm_lst tl
        | Print (e, _) -> "console.log(" ^ (comp_exp e) ^ ");" ^ comp_comm_lst tl
        | Inc (x, _) -> x ^ "++;" ^ (comp_comm_lst tl)
        | Dec (x, _) -> x ^ "--;" ^ (comp_comm_lst tl)
        | Decl (et, x, e) ->
            let create_str = match et with
                | VecTyp n -> "let " ^ x ^ "=vec" ^ (string_of_int n) ^ ".create();"
                | MatTyp (m, n) -> "let " ^ x ^ "=mat" ^ (string_of_int (max m n)) ^ ".create();"
                | _ -> "let "
            in
            create_str ^ (comp_assign x e) ^ (comp_comm_lst tl)
        | Assign (x, e) -> (comp_assign x e) ^ (comp_comm_lst tl)
        | AssignOp ((x, t), op, e) -> (comp_assign x ((Binop (op, (Var x, t), e)), t)) ^ (comp_comm_lst tl)
        | If (((b, _), c1), el, c2) -> 
            ("if " ^ "(" ^ (comp_exp b) ^ ")"
            ^ "{" ^ (comp_comm_lst c1) ^ "}"
            ^ (List.fold_left (fun acc ((b, _), c) -> "if " ^ "(" ^ (comp_exp b) ^ ")"
                ^ "{" ^ (comp_comm_lst c) ^ "}" ^ acc) "" el)
            ^ (match c2 with | Some c2 -> " else {" ^ (comp_comm_lst c2) ^ "}" | None -> "")
            ^ (comp_comm_lst tl))
        | For (i, (cond, _), after, cl) ->
            ("for (" ^ (comp_comm_lst [i]) ^ " " ^ (comp_exp cond) ^ "; " ^ (comp_comm_lst [after] |> (String.split_on_char ';') |> List.hd) ^ ")"
            ^ "{ " ^ (comp_comm_lst cl) ^ " }" ^ (comp_comm_lst tl))
        | Return Some (e, _) -> "return " ^ (comp_exp e) ^ ";" ^ (comp_comm_lst tl)
        | Return None -> "return;" ^ (comp_comm_lst tl)
        | FnCall (f, args) -> comp_comm_lst tl

let comp_fn (f : fn) : string =
    debug_print ">> comp_fn";
    let ((id, (p, rt, _)), cl) = f in
    let param_string = String.concat ", " (List.map (fun (i, t) -> i ^ ":" ^ (comp_type t)) p) in
    "function " ^ id ^ "(" ^ param_string ^ "):" ^ (comp_type rt) ^ "{" ^ (comp_comm_lst cl) ^ "}"

let rec comp_fn_lst (f : fn list) : string =
    debug_print ">> comp_fn_lst";
    match f with 
    | [] -> ""
    | h::t -> (comp_fn h) ^ (comp_fn_lst t)

let rec decl_attribs (gv : global_vars) : string = 
    debug_print ">> decl_attribs";
    match gv with
    | [] -> String.concat "" (List.map (fun n -> String.concat "" (List.map (fun t -> "var __" ^ t ^ n ^ "=" ^ t ^ n ^ ".create();") ["vec";"mat"])) ["2";"3";"4"])
    | (x, sq, et)::t -> match et with
        | VecTyp n -> "var " ^ x ^ "=vec" ^ (string_of_int n) ^ ".create();" ^ (decl_attribs t)
        | MatTyp (m,n) -> "var " ^ x ^ "=mat" ^ (string_of_int (max m n)) ^ ".create();" ^ (decl_attribs t)
        | _ -> "var " ^ x ^ ";" ^ (decl_attribs t)

let rec compile_program (prog : prog) (global_vars : global_vars) : string =
    debug_print ">> compile_programJS";
    "import {vec2,mat2,vec3,mat3,vec4,mat4} from 'gl-matrix';" ^ (decl_attribs global_vars) ^ (comp_fn_lst prog) ^ "main();"