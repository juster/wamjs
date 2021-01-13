"use strict";
(function(){

var exports = {
    parse, reset, dump, prog: compileP0, query: query0
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
var X = new Array(128) // registers (contain indices into Store)
var Xn = 0
var H // heap ptr
var ModeRd // true=read false=write
var S // address of next subterm to be matched
var Labels = {}
var P // instruction counter
reset()

function reset(){
    Store.fill(undefined), H = 0, X.fill(undefined), Xn = 0, ModeRd = true, S = H,
    Labels = {}, P = H
}

function resetRegs(){
    X.fill(0, Xn, undefined), Xn = 0
}

function dump(){
    var i
    console.log("==+-REGISTERS-+==")
    if(Xn == 0) console.log("(empty)")
    for(i=0; i<Xn; i++) console.log(i, X[i].toString())

    console.log("\n==+-HEAP-+==")
    if(H == 0) console.log("(empty)")
    for(i=0; i<H; i++) console.log(i, Store[i].toString())
}

/* Use new Cell(...) in order to give hints to JS interp to optimize ... */
const REF = 1, STR = 2, FUN = 3
function Cell(tag, a, b){
    if(typeof tag != "number"){ throw new Error("invalid tag") }
    this.tag = tag, this.a = a, this.b = b // a or b may be undefined
}
Cell.prototype.clone = function(){
    return new Cell(this.tag, this.a, this.b)
}
Cell.prototype.toString = function(){
    var tag
    switch(this.tag){
    case STR: tag="STR"; break
    case REF: tag="REF"; break
    }
    return (this.tag === FUN ? this.a+"/"+this.b : tag+" "+this.a)
}

function WamFail(){ Error.call(this, "WAM failure") }
WamFail.prototype = Object.assign({}, Error.prototype)

/* M0 MACHINE */
var M0 = {put_structure, set_variable, set_value}

/* Query instructions */
function put_structure(f, n, Xi){
    X[Xi] = Store[H] = new Cell(STR, H+1)
    Store[H+1] = new Cell(FUN, f, n)
    H+=2
}

function set_variable(Xi){
    X[Xi] = Store[H] = new Cell(REF, H), H++
}

function set_value(Xi){
    Store[H++] = X[Xi].clone()
}

/* Program instructions */
function get_structure(f, n, Xi){
    if(!ModeRd) return put_structure(f, n, Xi)

    var addr = deref(X[Xi].a)
    var cell = Store[addr]
    switch(cell.tag){
    case REF:
        Store[H+0] = new Cell(STR, H+1)
        Store[H+1] = new Cell(FUN, f, n)
        bind(addr, H)
        H+=2
        ModeRd = false
        break
    case STR:
        var a = cell.a
        if(Store[a].a === f && Store[a].b === n){
            S = a+1
            ModeRd = true
        }else{
            throw new WamFail()
        }
    }
}

function unify_variable(Xi){
    if(ModeRd){
        X[Xi] = Store[S]
    }else{
        X[Xi] = Store[H] = new Cell(REF, H)
        H++
    }
    S++
}

function unify_value(Xi){
    if(ModeRd){
        unify(Xi, S++)
    }else{
        Store[H++] = X[Xi].clone()
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

function compileQ0(s){
    resetRegs()
    ModeRd = false
    return compileQ0_(parse(s), {})
}

function compileQ0_(expr, seen){
    var k = exprK(expr)
    if(k in seen){
        set_value(seen[k])
    }else if(expr.struct){
        var Xi = Xn++
        for(var i=0; i<expr.n; i++){
            if(expr.args[i].struct) compileQ0_(expr.args[i], seen)
        }
        seen[k] = Xi
        put_structure(expr.atom, expr.n, Xi)
        for(var i=0; i<expr.n; i++){
            compileQ0_(expr.args[i], seen)
        }
    }else{
        set_variable(Xn)
        seen[k] = Xn++
    }
}

function compileP0(s){
    // XXX: do we reset registers?
    ModeRd = false
    return compileP0_(parse(s), {})
}

function compileP0_(expr, seen){
    var k = exprK(expr)
    if(k in seen){
        unify_value(seen[k])
    }else if(expr.struct){
        var Xi = Xn++
        seen[k] = Xi
        get_structure(expr.atom, expr.n, Xi)
        for(var i=0; i<expr.n; i++){
            compileQ0_(expr.args[i], seen)
        }
    }else{
        unify_variable(Xn)
        seen[k] = Xn++
    }
}

function query0(s){
    try{
        compileQ0(s)
        ModeRd = true
        compileP0
        return true
    }catch(err){
        if(err instanceof WamFail){
            return false
        }else{
            throw err
        }
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
            // sanity check
            throw new Error("insane")
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
var tok_regex = /([a-z][a-z_]*)|([A-Z_][a-z_]*)|([(),])|([ \t]+)|(\n+)/y
function tok(S0){
    var m, S
    S = {str:S0.str, i:S0.nexti, nexti:undefined}
    if(typeof S0.nexti == "undefined" || S0.nexti >= S0.str.length){
        S.next = null
        S.nexti = null
        return S
    }

    tok_regex.lastIndex = S0.nexti
    m = tok_regex.exec(S0.str)
    S.nexti = tok_regex.lastIndex
    if(S.nexti == 0) S.nexti = undefined
    if(!m){
        S.next = "unk"
    }else if(m[1]){
        S.next = {atom: m[1]}
    }else if(m[2]){
        S.next = {var: m[2]}
    }else if(m[3]){
        S.next = m[3]
    }else if(m[4]){
        // skip whitespace
        return tok(S)
    }else if(m[5]){
        S.next = "endl"
    }else{
        throw new Error("internal error")
    }
    return S
}

/* PARSER */
function parseArgs(S){
    var A = [], X

    while(true){
        switch(S.next){
        case ")":
            return [A, tok(S)]
        case "(": case null: case "endl": case "unk": case ",":
            throw new Error("syntax error at "+S.i)
        }
        X = parse2(S)
        A.push(X[0])
        S = X[1]

        // skip a single comma if it is the next token
        if(S.next === ","){
            S = tok(S)
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

    var S = tok(S0)
    if(S0.next.atom){
        if(S.next === "("){
            var X = parseArgs(tok(S)) // skip open paren
            S = X[1]
            return [{struct:true, atom:S0.next.atom, n:X[0].length, args:X[0]}, S]
        }else{
            return [{struct:true, atom:S0.next.atom, n:0, args:[]}, S]
        }
    }
    return [S0.next, S]
}

function parse(str){
    var S = tok({str:str, nexti:0}) // lookahead one token
    var X = parse2(S)
    if(X[1].next !== null){
        console.log(X[1])
        throw new Error("input should end at "+X[1].nexti)
    }else{
        return X[0]
    }
}

function exprK(expr){
    if(expr.atom){
        return "atom#"+expr.atom
    }else if(expr.struct){
        return "struct#"+expr.atom+"/"+expr.n
    }else if(expr.var){
        return "var#"+expr.var
    }else{
        throw new Error("unknown expr")
    }
}

})() // end module
