"use strict";
(function(){

var exports = {
    alloc: allocRegs, parse, reset, dump, prog: prog0, query: query0,
    exec: exec0
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
var ReadMode // true=read false=write
var S // address of next subterm to be matched
var Labels = {}
var P // instruction counter
reset()

var Ftbl = {}, Fn = 0 // functor table

/* heap tags */
const REF = 1, STR = 2, FUN = 3

/* instruction tags */
const PUT_STRUCT=8, SET_VAR=9, SET_VAL=10, GET_STRUCT=11, UNI_VAR=12,
    UNI_VAL=13

function die(msg){
    throw new Error(msg)
}

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
    var i, Frev = reverseF()

    if(X == Xbot && C == Cbot && H == Hbot) console.log("(empty)")
    for(i=0; i<X; i++) console.log(i, dumpStr(Store[i], Frev))
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

function dumpStr(cell, f){
    if(f === undefined) f = reverseF()
    if(cell === undefined) return "undefined"

    var str = tagNames.get(cell.tag) +" "+ cell.a
    if(cell.b !== undefined) str += ", "+ cell.b
    switch(cell.tag){
    case GET_STRUCT: case PUT_STRUCT: case FUN:
        str += " ("+f[cell.a]+")"
    }
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

function reverseF(){
    var Frev = []
    for(var i=0;i<Fn;i++){
        for(var f in Ftbl) if(Ftbl[f] == i){ Frev.push(f); break }
    }
    return Frev
}

/* a simulated memory cell */
function Cell(tag, a, b){
    if(typeof tag != "number"){ die("invalid tag") }
    this.tag=tag, this.a=a, this.b=b // a,b may be undefined
}
Cell.prototype.clone = function(){
    return new Cell(this.tag, this.a, this.b)
}

function WamFail(){ Error("wam failure") }
WamFail.prototype = Object.create({}, Error.prototype)

/* m0 interpreter */

function exec0(beg, end){
    ReadMode = true
    var H_ = H
    try{
        for(var i=beg; i<end; i++){
            console.log("*exec*", "S="+S, dumpStr(Store[i]))
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
        //H = H_
    }
}

var M0 = new Map([
    /* query instructions */
    [PUT_STRUCT, put_structure],
    [SET_VAR, set_variable],
    [SET_VAL, set_value],
    /* program instructions */
    [GET_STRUCT, get_structure],
    [UNI_VAR, unify_variable],
    [UNI_VAL, unify_value]
])

function put_structure(fi, Xi){
    Store[H] = new Cell(STR, H+1)
    Store[H+1] = new Cell(FUN, fi)
    Store[Xi] = Store[H].clone()
    H+=2
}

function set_variable(Xi){
    Store[H] = new Cell(REF, H)
    Store[Xi] = Store[H].clone()
    H++
}

function set_value(Xi){
    Store[H++] = Store[Xi].clone()
}

function get_structure(fi, Xi){
    if(!ReadMode) return put_structure(fi, Xi)

    var addr = deref(Xi)
    var cell = Store[addr]
    console.log("*get_struct*", dumpStr(cell))
    switch(cell.tag){
    case REF:
        Store[H+0] = new Cell(STR, H+1)
        Store[H+1] = new Cell(FUN, fi)
        bind(addr, H)
        H+=2
        ReadMode = false
        console.log("*DBG*", "write mode")
        break
    case STR:
        var a = cell.a
        if(Store[a].a == fi){
            S = a+1
            ReadMode = true
        }else{
            throw new WamFail()
        }
        break
    default:
        die("insane")
    }
}

function unify_variable(Xi){
    if(ReadMode){
        Store[Xi] = Store[S].clone()
    }else{
        Store[H] = new Cell(REF, H)
        Store[Xi] = Store[H].clone()
        H++
    }
    S++
}

function unify_value(Xi){
    if(ReadMode){
        unify(Xi, S)
    }else{
        Store[H++] = Store[Xi].clone()
    }
    S++
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

/* m0 compiler */

/* flatten a stream of tokens into registers of cells.
 *
 * registers are in the same order for both query and program compilation.
 * registers are assigned by walking the expression tree in a breadth-first
 * fashion.
 */
function allocRegs(expr){
    var regs=[], todo=[expr,0]
    X=1

    while(expr = todo.shift()){
        alloc(expr, todo.shift())
    }
    return regs

    function v(expr){
        var j
        if(!expr.var){
            die("insane")
        }else if((j = regs.indexOf(expr.var)) >= 0){
            return j
        }else{
            regs[X] = expr.var
            return X++
        }
    }

    function alloc(term, i){
        var j
        if(term.atom){
            // reserve space for arguments
            var args = term.args.map(t => {
                if(t.atom){
                    todo.push(t)
                    todo.push(X)
                    return X++
                }else{
                    return v(t)
                }
            })
            regs[i] = [term.atom].concat(args)
        }else{
            v(term)
        }
    }
}

function query0(str){
    var expr = parse(str)
    var C_ = C, H_ = H
    try{
        c(0, allocRegs(expr), {})
        S = H
        exec0(C_, C)
        dump()
        ReadMode = true
        console.log("executing prog")
        return exec0(Cbot, C_)
    }finally{
        C = C_, H = H_
    }

    function c(i, regs, seen){
        var atom
        if(i in seen){
            Store[C++] = new Cell(SET_VAL, i)
        }else if(Array.isArray(regs[i])){
            seen[i] = true
            for(var j=1; j<regs[i].length; j++){
                var k = regs[i][j]
                if(Array.isArray(regs[k])) c(k, regs, seen)
            }
            var atom = regs[i][0]
            var n = regs[i].length-1
            Store[C++] = new Cell(PUT_STRUCT, findF(atom, n), i)
            for(var j=1; j<regs[i].length; j++){
                var k = regs[i][j]
                /*if(!Array.isArray(regs[k]))*/ c(k, regs, seen)
            }
        }else{
            seen[i] = true
            Store[C++] = new Cell(SET_VAR, i)
        }
    }
}

function prog0(str){
    c(0, allocRegs(parse(str)), {})
    dump()

    function c(i, regs, seen){
        if(Array.isArray(regs[i])){
            seen[i] = true
            var term = regs[i], atom = term[0], n = regs[i].length-1
            Store[C++] = new Cell(GET_STRUCT, findF(atom, n), i)
            for(var j=1; j<term.length; j++){
                if(seen[term[j]]){
                    Store[C++] = new Cell(UNI_VAL, term[j])
                }else{
                    Store[C++] = new Cell(UNI_VAR, term[j])
                    seen[term[j]] = true
                }
            }
            for(var j=1; j<term.length; j++){
                var k = term[j]
                if(Array.isArray(regs[k])) c(k, regs, seen)
            }
        }else if(seen[i]){
            Store[C++] = new Cell(UNI_VAL, i)
        }else{
            Store[C++] = new Cell(UNI_VAR, i)
            seen[i] = true
        }
    }
}

function deref(a){
    var i
    for(var i=a, cell=Store[i]; cell.tag==REF; i=cell.a){
        if(cell.a == i) break
        console.log("*deref* i="+i)
    }
    return i
}

/* "... a unification algorithm based on the UNION/FIND method [AHU74] ..." */
function unify(i1, i2){
    var S = [i1, i2]
    while(S.length > 0){
        console.log("*unify*", S, d1, d2)
        var d1 = deref(S.pop()), d2 = deref(S.pop())
        if(d1 == d2) continue

        var cell1 = Store[d1], cell2 = Store[d2]
        if(cell1.tag == REF || cell2.tag == REF){
            bind(d1, d2)
            continue
        }

        /* unify both structures */
        if(cell1.tag != STR || cell2.tag != STR){
            die("insane") // sanity check
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
    else die("internal error")
    
    return S
}

/* PARSER */

function parse(str){
    var S = next({str:str, nexti:0}) // lookahead one token
    var A = parse2(S)
    if(A[1].peek !== null){
        console.log(A[1])
        throw die("input should end at "+A[1].nexti)
    }else{
        return A[0]
    }

    function parse2(S0){
        switch(S0.peek){
        case null: case "endl":
            return [null,S0]
        case "ws":
            die("internal error")
        case "unk":
            die("unknown char at "+S0.i)
        case "(": case ")":
            die("syntax error at "+S0.i)
        }

        var S = next(S0)
        if(S0.peek.atom){
            if(S.peek === "("){
                var A = parseArgs(next(S)) // skip open paren
                S = A[1]
                return [{atom:S0.peek.atom, n:A[0].length, args:A[0]}, S]
            }else{
                return [{atom:S0.peek.atom, n:0, args:[]}, S]
            }
        }
        return [S0.peek, S]
    }

    function parseArgs(S){
        var A = [], B

        while(true){
            switch(S.peek){
            case "(": case ")": case null: case "endl": case "unk": case ",":
                die("syntax error at "+S.i)
            }
            B = parse2(S)
            A.push(B[0])
            S = B[1]

            switch(S.peek){
            case ")": return [A, next(S)]
            case ",": S = next(S); break // skip a single comma
            }
        }
    }
}

})() // end module
