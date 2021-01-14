"use strict";
(function(){

var exports = {
    parse, reset, dump, prog: compileP0, query: parseQ,
    exec: exec0, flatten
}

if(typeof module !== "undefined"){
    module.exports = exports
}else if(typeof globalThis !== "undefined"){
    globalThis.wam = exports
}else if(typeof self !== "undefined"){
    self.wam = exports
}else if(typeof window !== "undefined"){
    window.wam = exports
}

var Store = new Array(1024) // simulates main memory
const Xbot = 1
var X // register ptr
const Xtop = 128, Cbot = Xtop
var C // code ptr
const Ctop = Xtop+128, Hbot = Ctop
var H // heap ptr
var ModeRd // true=read false=write
var S // address of next subterm to be matched
var Labels = {}
var P // instruction counter
reset()

var Ftbl = {}, Fn = 0 // functor table

/* Heap tags */
const REF = 1, STR = 2, FUN = 3

/* Instruction tags */
const PUT_STRUCT=8, SET_VAR=9, SET_VAL=10, GET_STRUCT=11, UNI_VAR=12,
    UNI_VAL=13

function reset(){
    Store.fill(undefined, Xbot, X)
    Store.fill(undefined, Cbot, C)
    Store.fill(undefined, Hbot, H)
    Ftbl = {}, Fn = 0,  X = Xbot, C = Cbot, H = Hbot, S = H, Labels = {}
    S = H, P = C
}

function resetRegs(){
    Store.fill(undefined, Xbot, X)
    X = Xbot
}

function dump(){
    var i
    //if(X == 0) console.log("(empty)")
    var Frev = []
    for(i=0;i<Fn;i++){
        for(var f in Ftbl) if(Ftbl[f] == i){ Frev.push(f); break }
    }
    if(X == 0 && H == Hbot) console.log("(empty)")
    //for(i=0; i<X; i++) console.log(i, dumpStr(Store[i], Frev))
    for(i=Cbot; i<C; i++) console.log(i, dumpStr(Store[i], Frev))
    for(i=Hbot; i<H; i++) console.log(i, dumpStr(Store[i], Frev))

    for(i=0;i<Frev.length;i++) console.log(i, Frev[i])
}

var tagNames = new Map([
    [STR,"STR"],
    [REF,"REF"],
    [FUN,"FUN"],
    [PUT_STRUCT,"PUT_STRUCT"],
    [SET_VAR,"SET_VAR"],
    [SET_VAL,"SET_VAL"],
    [GET_STRUCT,"GET_STRUCT"],
    [UNI_VAR,"UNI_VAR"],
    [UNI_VAL,"UNI_VAL"]
])

function dumpStr(cell, F){
    var str = tagNames.get(cell.tag) +" "+ cell.a
    if(cell.b !== undefined) str += ", "+ cell.b
    if(cell.tag == FUN) str += " ("+F[cell.a]+")"
    return str
}

function findF(f, n){
    var k = f+"/"+n
    if(k in Ftbl){
        return Ftbl[k]
    }else{
        return Ftbl[k] = Fn++
    }
}

/* a simulated memory cell */
function Cell(tag, a, b){
    if(typeof tag != "number"){ throw new Error("invalid tag") }
    this.tag=tag, this.a=a, this.b=b // a,b may be undefined
}
Cell.prototype.clone = function(){
    return new Cell(this.tag, this.a, this.b)
}

function WamFail(){ Error("WAM failure") }
WamFail.prototype = Object.create({}, Error.prototype)

/* M0 INTERPRETER */

function exec0(){
    var H0 = H
    try{
        for(var i=Cbot; i<C; i++){
            var f = M0.get(Store[i].tag)
            f(Store[i].a, Store[i].b)
        }
        return true
    }catch(err){
        if(err instanceof WamFail){
            return false
        }else{
            throw(err)
        }
    }finally{
        //H = H0
    }
}

var M0 = new Map([
    /* Query instructions */
    [PUT_STRUCT, put_structure],
    [SET_VAR, set_variable],
    [SET_VAL, set_value],
    /* Program instructions */
    [GET_STRUCT, get_structure],
    [UNI_VAR, unify_variable],
    [UNI_VAL, unify_value]
])

function put_structure(fi, Xi){
    Store[Xi] = Store[H] = new Cell(STR, H+1)
    Store[H+1] = new Cell(FUN, fi)
    H+=2
}

function set_variable(Xi){
    Store[Xi] = Store[H] = new Cell(REF, H), H++
}

function set_value(Xi){
    Store[H++] = Store[Xi].clone()
}

function get_structure(fi, Xi){
    if(!ReadMode) return put_structure(fi, Xi)

    var addr = deref(Store[Xi].a)
    var cell = Store[addr]
    switch(cell.tag){
    case REF:
        Store[H+0] = new Cell(STR, H+1)
        Store[H+1] = new Cell(FUN, f, n)
        bind(addr, H)
        H+=2
        ReadMode = false
    case STR:
        var a = cell.a
        if(Store[a].a == fi){
            S = a+1
            ReadMode = true
        }else{
            throw new WamFail()
        }
    }
}

function unify_variable(Xi){
    if(ReadMode){
        Store[Xi] = Store[S]
    }else{
        Store[Xi] = Store[H] = new Cell(REF, H)
        H++
    }
    S++
}

function unify_value(Xi){
    if(ReadMode){
        unify(Xi, S++)
    }else{
        Store[H++] = Store[Xi].clone()
    }
}

function bind(i, j){
    if(Store[i].tag == REF && Store[i].a == i){
        Store[i].a = j
    }else if(Store[j].tag == REF && Store[j].a == j){
        Store[j].a = i
    }else{
        throw new WamFail()
    }
}

/* M0 COMPILER */

function compileQ0(str){
    resetRegs()
    compileQ0_(tokenize(str))
}

function synerr(S){
    die("syntax error: column "+S.nexti)
}

function die(msg){
    throw new Error(msg)
}

function parseQ(str){
    return parseQ_(tokenize(str))
}

function pclose(S, A){
    console.log("pclose")
    var n = 0, i = S.nexti

    S = next(S)
    while(true){
        console.log(JSON.stringify(S))
        switch(S.peek){
        case null: die("unclosed paren: col "+i)
        case "(": n++; S = next(S); continue
        case ")": case ",": synerr(S)
        }

        A.push(S.peek)

        S = next(S)
        switch(S.peek){
        case ",": S = next(S); break
        case ")": S = next(S); if(n == 0) return S; n--
        }
    }
}

function adv(S0, A){
    var S = next(S0)
    A.unshift(S.peek)
    return S
}

/* Flatten a stream of tokens into registers of cells.
 *
 * Registers are in the same order for both query and program compilation.
 * Registers are assigned by walking the expression tree in a breadth-first
 * fashion.
 */
function flatten(str){
    var S=tokenize(str)
    var regs=[], tok, toks=[S.peek]
    resetRegs()

    console.log("DBG",S)

    while(tok = toks.shift()){
        switch(tok){ case ",": case "(": case ")": synerr(S) }
        regs.push(tok)
        if(tok.atom){
            /* "(" is only allowed after an atom */
            S = adv(S, toks)
            if(toks[0] === "("){
                toks.shift()
                S = pclose(S, toks)
            }
        }
        S = adv(S, toks)
    }

    return regs
}

function compileQ0_old(expr, regs, seen){
    if(!seen) return compileQ0_(expr, regs, {}) // top-level call

    var Xi = regs[exprK(expr)]
    if(Xi === undefined) throw new Error("insane")
    if(seen[Xi]){
        Store[C++] = new Cell(SET_VAL, Xi)
    }else if(expr.struct){
        var fi = findF(expr.atom, expr.n)
        seen[Xi] = true

        /* Queries place any structure-terms before this structure. */
        for(var i=0; i<expr.n; i++){
            if(expr.args[i].struct){
                compileQ0_(expr.args[i], seen, regs)
            }
        }
        Store[C++] = new Cell(PUT_STRUCT, fi, Xi)
        for(var i=0; i<expr.n; i++){
            compileQ0_(expr.args[i], seen)
        }
    }else{
        Store[C++] = new Cell(SET_VAR, Xi)
        seen[Xi] = true
    }
}

function compileP0(s){
    return compileP0_(parse(s), {})
}

function compileP0_(expr, seen){
    var k = exprK(expr)
    if(k in seen){
        Store[C++] = new Cell(UNI_VAL, seen[k])
    }else if(expr.struct){
        var Xi = X++
        var fi = findF(expr.atom, expr.n)
        seen[k] = Xi
        Store[C++] = new Cell(GET_STRUCT, fi, Xi)
        /* Programs place any structure-terms after this structure. */
        for(var i=0; i<expr.n; i++){
            compileQ0_(expr.args[i], seen)
        }
    }else{
        Store[C++] = new Cell(UNI_VAR, X)
        seen[k] = X++
    }
}

function query0(s){
    var H_ = H
    try{
        compileQ0(s)
        S = Hbot
        return true
    }catch(err){
        if(err instanceof WamFail){
            return false
        }else{
            throw err
        }
    }finally{
        H = H_
    }
}

function deref(i){
    while(true){
        console.log("*DBG* i="+i)
        var cell = Store[i]
        if(cell.tag != REF){
            return i
        }else if(cell.a == i){
            return i
        }else{
            i = cell.a
        }
    }
}

/* "... a unification algorithm based on the UNION/FIND method [AHU74] ..." */
function unify(i1, i2){
    var S = [i1, i2]
    while(S.length > 0){
        var d1 = deref(S.pop()), d2 = deref(S.pop())
        if(d1 == d2) continue

        var cell1 = Store[d1], cell2 = Store[d2]
        if(cell1.tag == REF || cell2.tag == REF){
            bind(d1, d2)
            continue
        }

        /* unify both structures */
        if(cell1.tag != STR || cell2.tag != STR){
            throw new Error("insane") // sanity check
        }
        var fn1 = Store[cell1.a], fn2 = Store[cell2.a]
        if(fn1.a === fn2.a && fn1.b === fn2.b){
            /* structures match */
            for(var i=1, n=fn1.b; i<=n; i++){
                /* unify functor parameters */
                S.push(cell1.a+i)
                S.push(cell2.a+i)
            }
        }else{
            throw new WamFail()
        }
    }
}

/* TOKENIZER */
function tokenize(str){
    return next({str, nexti:0})
}

var tok_regex = /([a-z][a-z_]*)|([A-Z_][a-z_]*)|([(),])|([ \t]+)|(\n+)/y
function next(S0){
    if(S0.peek === null) return S0
    if(typeof S0.nexti != "number") die("insane")
    
    var m, S
    S = {str:S0.str, i:S0.nexti, nexti:undefined}
    if(S0.nexti >= S0.str.length){ S.peek = null; return S }

    tok_regex.lastIndex = S0.nexti
    m = tok_regex.exec(S0.str)
    S.nexti = tok_regex.lastIndex

    if(!m) S.peek = "unk"
    else if(m[1]) S.peek = {atom: m[1]}
    else if(m[2]) S.peek = {var: m[2]}
    else if(m[3]) S.peek = m[3]
    else if(m[4]) return next(S) // skip whitespace
    else if(m[5]) S.peek = null // was "endl"
    else throw new Error("internal error")
    
    console.log("DBG",S)
    return S
}

/* PARSER */
function parseArgs(S){
    var A = [], B

    while(true){
        switch(S.peek){
        case ")":
            return [A, next(S)]
        case "(": case null: case "endl": case "unk": case ",":
            throw new Error("syntax error at "+S.i)
        }
        B = parse2(S)
        A.push(B[0])
        S = B[1]

        // skip a single comma if it is the next token
        if(S.peek === ","){
            S = next(S)
        }
    }
}

function parse2(S0){
    switch(S0.next){
    case null: case "endl":
        return [null,S0]
    case "ws":
        throw new Error("internal error")
    case "unk":
        throw new Error("unknown char at "+S0.i)
    case "(": case ")":
        throw new Error("syntax error at "+S0.i)
    }

    var S = next(S0)
    if(S0.next.atom){
        if(S.peek === "("){
            var A = parseArgs(next(S)) // skip open paren
            S = A[1]
            return [{struct:true, atom:S0.next.atom, n:A[0].length, args:A[0]}, S]
        }else{
            return [{struct:true, atom:S0.next.atom, n:0, args:[]}, S]
        }
    }
    return [S0.next, S]
}

function parse(str){
    var S = next({str:str, nexti:0}) // lookahead one token
    var A = parse2(S)
    if(A[1].next !== null){
        console.log(A[1])
        throw new Error("input should end at "+A[1].nexti)
    }else{
        return A[0]
    }
}

function exprK(expr){
    if(expr.struct){
        return "fun#"+findF(expr.atom, expr.n)
    }else if(expr.var){
        return "var#"+expr.var
    }else{
        throw new Error("unknown expr")
    }
}

})() // end module
