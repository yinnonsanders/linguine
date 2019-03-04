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

(* Note the column parameter for padding the matrix size *)
let rec string_of_no_paren_vec (v: exp list) (padding: int) : string = 
    (String.concat ", " (List.map comp_exp v)) ^ (repeat ", 0." padding)
  
and string_of_mat (m: exp list list) : string = 
    (* Note the transpose to match the glsl column-oriented style *)
    let tm = Lin_ops.transpose m in
    let r = (List.length tm) in
    let c = (if r = 0 then 0 else List.length (List.hd tm)) in
    let max_dim = max r c in
    let string_of_vec_padded = (fun v -> (string_of_no_paren_vec v (max_dim - List.length v))) in
    "mat" ^ (string_of_int max_dim) ^ ".fromValues(" ^ (String.concat ", " (List.map string_of_vec_padded tm)) ^
    (repeat (string_of_no_paren_vec [] max_dim) (max_dim - List.length tm)) ^ ")"

and call_lib_func (t : string) (f : string) (args : exp list) : string =
    "__" ^ t ^ f ^ "(" ^ (String.concat "," (List.map comp_exp args)) ^ ")"

and comp_exp (e : exp) : string =
    match e with
    | Val v -> comp_value v
    | Var x -> x
    | Arr a -> (match a with
        | [] -> failwith "cannot have an empty array"
        | (_, t)::_ -> (match t with
            | FloatTyp | IntTyp -> "vec" ^ (string_of_int (List.length a)) ^ ".fromValues(" ^ (String.concat ", " (List.map (fun (e, t) -> comp_exp e) a)) ^ ")"
            | VecTyp n -> let as_vec_list = (fun v -> (match v with | (Arr a', _) -> (List.map fst a') | _ -> failwith "Typechecker error, a matrix must be a list of vectors")) in
                string_of_mat (List.map as_vec_list a)
            | _ -> failwith "Typechecker error, every array must be a list of ints, floats, or vectors"))
    | Unop (op, (e, t)) ->
        begin
            match t with
            | VecTyp n ->
                begin
                    match op with
                    | Neg -> call_lib_func ("vec" ^ (string_of_int n)) "negate" [e]
                    | _ -> failwith "Cannot apply this operator to vector"
                end
            | MatTyp (m, n) ->
                begin
                    match op with
                    | Neg -> comp_exp (Binop (Times, (Val (Num (-1)), IntTyp), (e,t)))
                    | _ -> failwith "Cannot apply this operator to matrix"
                end
            | _ -> string_of_unop op (comp_exp e)
        end
    | Binop (op, (e1, t1), (e2, t2)) ->
        begin
            match t1, t2 with
            | VecTyp n, VecTyp _ ->
                let typ_string = "vec" ^ (string_of_int n) in
                if op = Eq then typ_string ^ ".equals(" ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
                else
                    let op_string = match op with
                        | Plus -> "add"
                        | Minus -> "sub"
                        | Div -> "div"
                        | CTimes  -> "mul"
                        | _ -> failwith ("Cannot apply " ^ (binop_string op) ^ " to vectors")
                    in
                    call_lib_func typ_string op_string [e1;e2]
            | IntTyp, VecTyp n | FloatTyp, VecTyp n ->
                let scalar = match op with
                    | Times -> e1
                    | Div -> Binop (Div, ((Val (Num 1)), IntTyp), (e1, t1))
                    | _ -> failwith ("Cannot apply " ^ (binop_string op) ^ " to vector and scalar")
                in
                call_lib_func ("vec" ^ (string_of_int n)) "scale" [e2;scalar]
            | VecTyp n, IntTyp | VecTyp n, FloatTyp ->
                let scalar = match op with
                    | Times -> e2
                    | Div -> Binop (Div, ((Val (Num 1)), IntTyp), (e2, t2))
                    | _ -> failwith ("Cannot apply " ^ (binop_string op) ^ " to vector and scalar")
                in
                call_lib_func ("vec" ^ (string_of_int n)) "scale" [e1;scalar]
            | MatTyp (ldim, _), VecTyp rdim ->
                let typ_string = "vec" ^ (string_of_int rdim) in
                if ldim = rdim then call_lib_func typ_string ("transformMat" ^ (string_of_int rdim)) [e2;e1]
                else ""
            | IntTyp, MatTyp (m,n) | FloatTyp, MatTyp (m,n) ->
                call_lib_func ("mat" ^ (string_of_int (max m n))) "multiplyScalar" [e2;e1]
            | MatTyp (m,n), IntTyp | MatTyp (m,n), FloatTyp ->
                call_lib_func ("mat" ^ (string_of_int (max m n))) "multiplyScalar" [e1;e2]
            | MatTyp (ldim, _), MatTyp (_, rdim) ->
                let typ_string = "mat" ^ (string_of_int (max ldim rdim)) in
                if op = Eq then typ_string ^ ".equals(" ^ (comp_exp e1) ^ "," ^ (comp_exp e2) ^ ")"
                else
                    let op_string =
                        match op with
                        | Plus -> "add"
                        | Minus -> "sub"
                        | Div -> "div"
                        | Times  -> "mul"
                        | _ -> failwith ("Cannot apply " ^ (binop_string op) ^ " to matrices")
                    in
                    call_lib_func typ_string op_string [e1;e2]
                (* if ldim = rdim then call_lib_func typ_string "mul" [e1;e2]
                else "" *)
            | _ -> "(" ^ string_of_binop op (comp_exp e1) (comp_exp e2) ^ ")"
        end
    | FnInv (f, args) -> f ^ "(" ^ (String.concat "," (List.map comp_exp args)) ^ ")"

(* let comp_assign_mat_vec (x : id) (e : exp) (typ_str : string) (n : int) : string =
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
    typ_str ^ (string_of_int n) ^ "." ^ func ^ "(" ^ x ^ "," ^ args ^ ");" *)

let comp_assign (x : id) ((e, t) : texp) : string =
    match t with
    | UnitTyp | BoolTyp | IntTyp | FloatTyp -> x ^ "=" ^ (comp_exp e) ^ ";"
    | VecTyp v -> "vec" ^ (string_of_int v) ^ ".copy(" ^ x ^ "," ^ (comp_exp e) ^ ");"
    | MatTyp (m, n) -> "mat" ^ (string_of_int (max m n)) ^ ".copy(" ^ x ^ "," ^ (comp_exp e) ^ ");"
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
        | FnCall (f, args) -> f ^ "(" ^ (String.concat "," (List.map comp_exp args)) ^ ");" ^ (comp_comm_lst tl)

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
    | [] -> ""
    | (x, sq, et)::t -> match et with
        | VecTyp n -> "var " ^ x ^ "=vec" ^ (string_of_int n) ^ ".create();" ^ (decl_attribs t)
        | MatTyp (m,n) -> "var " ^ x ^ "=mat" ^ (string_of_int (max m n)) ^ ".create();" ^ (decl_attribs t)
        | _ -> "var " ^ x ^ ";" ^ (decl_attribs t)

let util_funcs =
    String.concat "" (List.map
        (fun (t, f, args) ->
            "function __" ^ t ^ f ^ "(" ^ args ^ "):" ^ t ^ "{var out=" ^ t ^ ".create();" ^ t ^ "." ^ f ^ "(out," ^ args ^ ");return out;}")
        [
            ("vec2", "add", "a,b");
            ("vec2", "sub", "a,b");
            ("vec2", "mul", "a,b");
            ("vec2", "negate", "a");
            ("vec2", "scale", "a,b");
            ("vec2", "transformMat2", "a,m");
            ("vec3", "add", "a,b");
            ("vec3", "sub", "a,b");
            ("vec3", "mul", "a,b");
            ("vec3", "negate", "a");
            ("vec3", "scale", "a,b");
            ("vec3", "transformMat3", "a,m");
            ("vec4", "add", "a,b");
            ("vec4", "sub", "a,b");
            ("vec4", "mul", "a,b");
            ("vec4", "negate", "a");
            ("vec4", "scale", "a,b");
            ("vec4", "transformMat4", "a,m");
            ("mat2", "add", "a,b");
            ("mat2", "sub", "a,b");
            ("mat2", "mul", "a,b");
            ("mat2", "multiplyScalar", "a,b");
            ("mat3", "add", "a,b");
            ("mat3", "sub", "a,b");
            ("mat3", "mul", "a,b");
            ("mat3", "multiplyScalar", "a,b");
            ("mat4", "add", "a,b");
            ("mat4", "sub", "a,b");
            ("mat4", "mul", "a,b");
            ("mat4", "multiplyScalar", "a,b");
        ])

let rec compile_program (prog : prog) (global_vars : global_vars) : string =
    debug_print ">> compile_programJS";
    "import {vec2,mat2,vec3,mat3,vec4,mat4} from 'gl-matrix';" ^ util_funcs ^ "\n" ^ (decl_attribs global_vars) ^ (comp_fn_lst prog) ^ "main();"