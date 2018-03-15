/* 
TODOLIST:
basic ok!
  tokenizing & parsing
  eval-apply metacircular model
  environment
the implementation of undefined
declaration hoisting: making the defined variable referable in the entire block
separation of syntactic analysis from eval to avoid too much repeated analysis during execution
lazy-evaluation
repl and the loop
*/

class ASTNode {
  constructor(proc, args) {
    this.proc = proc
    this.args = args
  }
}

class Frame {
  constructor(bindings) {
    this.bindings = bindings || {}
  }
  set(name, value) {
    this.bindings[name] = value
  }
  get(name) {
    return this.bindings[name]
  }
}

class Environment {
  constructor(env, frame) {
    this.frame = frame
    this.parent = env
    this.get = function get(name) {
      var result = this.frame.get(name)
      if (result !== undefined) {
        return result
      } else {
        if (this.parent) {
          return get.call(this.parent, name)
        } else {
          throw `Unbound variable ${name}`
        }
      }
    }
    this.set = function set(name, value) {
      var result = this.frame.get(name)
      if (result !== undefined) {
        this.frame.set(name, value)
      } else {
        if (this.parent) {
          return set.call(this.parent, name, value)
        } else {
          throw `Cannot set undefined variable ${name}`
        }
      }
    }
  }
  extend(frame) {
    var env = new Environment(this, frame)
    return env
  }
  defineVariable(name, value) {
    this.frame.set(name, value)
  }
}

var _parse = (tokens) => {
  if (tokens.length == 0) {
    throw 'Unexpected EOF'
  }
  var token = tokens.shift()
  if (token == '(') {
    var stack = []
    while (tokens[0] != ')') {
      stack.push(_parse(tokens))
    }
    tokens.shift()
    var proc = stack.shift()
    return new ASTNode(proc, stack)
  } else if (token == ')') {
    throw 'Unexpected )'
  } else {
    return token
  }
}

var lisp_parse = (code) => {
  code = lisp_beautify(code)
  var tokens = lisp_tokenize(code)
  var ast = []
  while (tokens.length > 0) {
    ast.push(_parse(tokens))
  }
  return ast
}

// format the source code for better tokenizing
var lisp_beautify = (code) => {
  return code
  .replace(/\n/g, ' ') // replace line-breaks with spaces
  .replace(/\(/g, ' ( ') // append one space into each side of a left parenthesis
  .replace(/\)/g, ' ) ') // append one space into each side of a right parenthesis
  .replace(/\s{2,}/g, ' ') // shrink any space sequences longer than 2 into a single space
  .replace(/^\s/, '') // remove space on the head of the source code
  .replace(/\s$/, '') // remove space on the tail of the source code
}

var lisp_tokenize = (code) => {
  return code.split(' ')
}

// print out a lisp ast node
var lisp_stringify = (ast) => {
  if (ast && ast.constructor && ast.constructor.name == 'ASTNode') {
    var proc = lisp_stringify(ast.proc)
    var args = ast.args.map(lisp_stringify).join(' ')
    return `(${proc} ${args})`
  } else {
    if (Array.isArray(ast)) {
      return ast.map(lisp_stringify).join(' ')
    } else {
      return ast
    }
  }
}

// evaluate the lisp source code and return the result
var lisp_eval = (code) => {
  var ast = lisp_parse(code)
  var output = _lisp_eval(ast, globalEnvironment) // todo: the environment should be a parameter
  return output
}

// primitive implementations
var theEmptyList = []
var cons = (a, b) => [a, b]
var car = (a) => a[0]
var cdr = (a) => a[1]
var list = (...elements) => {
  if (elements.length == 0) {
    return theEmptyList
  } else {
    var head = elements.shift()
    return cons(head, list.apply(null, elements))
  }
}

// primitive procedures (primitive values is excluded here, which are later added into the global environment)
const PRIMITIVES_PROCEDURES = {
  '+': (a, b) => a + b,
  '-': (a, b) => a - b,
  '*': (a, b) => a * b,
  '/': (a, b) => a / b,
  '>': (a, b) => a > b,
  '<': (a, b) => a < b,
  '=': (a, b) => a == b,
  '?:': (a, b, c) => a ? b : c, // added an operator for simulating tenary operator in other languages
  'display': (...args) => console.log.apply(null, args),
  'and': (a, b) => a && b,
  'or': (a, b) => a || b,
  'not': (a) => !a,
  'null?': (a) => Array.isArray(a) && a.length == 0,
  'cons': cons,
  'car': car,
  'cdr': cdr,
  'list': list,
}

for(var name in PRIMITIVES_PROCEDURES) {
  var proc = PRIMITIVES_PROCEDURES[name]
  proc.isPrimitive = true
}

var _lisp_eval = (ast, env) => {
  return _eval(ast, env)
}

// evaluate a subexpression in a given environment
var _eval = (ast, env) => {
  if (_isNumber(ast)) {
    return _evalNumber(ast)
  } else if (_isString(ast)) {
    return _evalString(ast)
  } else if (_isVariable(ast)) {
    return _lookUp(ast, env)
  } else if (_isAssign(ast)) {
    return _evalAssign(ast, env)
  } else if (_isDefine(ast)) {
    return _evalDefine(ast, env)
  } else if (_isLet(ast)) {
    return _eval(_letToLambdaWithArgs(ast), env)
  } else if (_isIf(ast)) {
    return _evalIf(ast, env)
  } else if (_isCond(ast)) {
    return _eval(_condToIf(ast), env)
  } else if (_isLambda(ast)) {
    return _makeLambda(ast, env)
  } else if (_isSequence(ast)) {
    return _evalSequence(ast, env)
  } else if (_isBegin(ast)) {
    return _evalBegin(ast, env)
  } else if (_isApply(ast)) {
    var proc = _eval(ast.args[0], env)
    var args = _flatten(_eval(ast.args[1], env))
    return _apply(proc, args)
  // if its a procedure (a non-special expression)
  // evaluate its operator(proc) and operands(args), and do the application
  } else if (_isProcedure(ast)){
    var proc = _eval(ast.proc, env)
    var args = ast.args.map((arg) => _eval(arg, env))
    return _apply(proc, args)
  } else {
    throw `Unknown expression ${lisp_stringify(ast)}`
  }
}

var _isVariable = (ast) => {
  return typeof ast == 'string' && ast[0] != '`'
}

var _lookUp = (ast, env) => {
  return env.get(ast)
}

var _isProcedure = (ast) => {
  return ast && ast.constructor && ast.constructor.name == 'ASTNode'
}

var _isPrimitive = (proc) => {
  return proc && proc.isPrimitive
}

var _isApply = (ast) => {
  return ast.proc == 'apply'
}

// apply a procedure: if it's primitive, apply directly
// else, because the body of the procedure is an expression to be evaluated
// we extend the environment of the procedure by creating bindings between formal parameters and actual arguments
// and evaluate the body in the extended new environment
var _apply = (proc, args) => {
  if (_isPrimitive(proc)) {
    return _applyPrimitive(proc, args)
  } else {
    var bindings = _bind(proc.params, args)
    var frame = new Frame(bindings)
    var newEnv = proc.env.extend(frame)
    return _eval(proc.body, newEnv)
  }
}

// binds a bunch of formal parameters to its corresponding actual arguments
var _bind = (params, args) => {
  var bindings = {}
  if (params) {
    for (var i = 0; i < params.length; i++) {
      var param = params[i]
      var arg = args[i]
      bindings[param] = arg
    }
  }
  return bindings
}

var _applyPrimitive = (proc, args) => {
  return proc.apply(null, args)
}

var _isNumber = (ast) => {
  return /^[0-9]+$/.test(ast)
}

var _evalNumber = (ast) => {
  return parseInt(ast)
}

var _isString = (ast) => {
  return ast[0] == '`'
}

var _evalString = (ast) => {
  return ast.slice(1)
}

// return the flattened array (a one-dimensionalized array with any extra nesting removed)
var _flatten = (arr) => {
  return arr.reduce((a, b) => {
    if (Array.isArray(b)) {
      return a.concat(_flatten(b))
    } else {
      a.push(b)
      return a
    }
  }, [])
}

var _evalPrimitive = (ast) => {
  return PRIMITIVES_PROCEDURES[ast]
}

var _isDefine = (ast) => {
  return ast.proc == 'define'
}

var _evalDefine = (ast, env) => {
  var name = ast.args[0]
  // to support the (define (procName procParams) (procBody)) syntatic sugar
  if (_isProcedure(name)) {
    ast = _defineProcToDefine(ast)
    name = ast.args[0]
  }
  var value = _eval(ast.args.slice(1), env)
  env.defineVariable(name, value)
  return 'define ok!'
}

var _defineProcToDefine = (ast) => {
  var procName = ast.args[0].proc
  var procParams = ast.args[0].args.slice(0)
  var procBody = ast.args.slice(1)

  var firstParam = procParams.shift()
  var paramNode = new ASTNode(firstParam, procParams)
  var lambdaNode = new ASTNode('lambda', [paramNode, procBody])
  return new ASTNode('define', [procName, lambdaNode])
}

var _isAssign = (ast) => {
  return ast.proc == 'set!'
}

var _evalAssign = (ast, env) => {
  var name = ast.args[0]
  var value = _eval(ast.args.slice(1), env)
  env.set(name ,value)
  return `set ${name} ${value} ok!`
}

var _isLet = (ast) => {
  return ast.proc == 'let'
}

var _letToLambdaWithArgs = (ast, env) => {
  var firstArg = ast.args[0].proc.proc
  var restArgs = ast.args[0].args
  if (restArgs && restArgs.length > 0) {
    restArgs = restArgs.map(_ast => _ast.proc)
  } else {
    restArgs = []
  }

  var args = [firstArg]
  if (restArgs && restArgs.length != 0) {
    args = args.concat(restArgs)
  }

  var lambda = _letToLambda(ast)
  var result = new ASTNode(lambda, args)

  return new ASTNode(lambda, args)
}

var _letToLambda = (ast) => {
  var firstParam = ast.args[0].proc.proc
  var restParam = ast.args[0].args.map(arg => arg.proc)
  var param = new ASTNode(firstParam, restParam)
  var body = ast.args.slice(1)
  var lambda = new ASTNode('lambda', [param, body])
  return lambda
}

var _isIf = (ast) => {
  return ast.proc == 'if'
}

var _evalIf = (ast, env) => {
  var predResult = _eval(ast.args[0], env)
  if (predResult) {
    return _eval(ast.args[1], env)
  } else {
    return _eval(ast.args[2], env)
  }
}

var _isCond = (ast) => {
  return ast.proc == 'cond'
}

var _condToIf = (ast) => {
  var clauses = ast.args

  var predicates = clauses.map((clause) => clause.proc)
  var actions = clauses.map((clause) => clause.args)

  return __condToIf(predicates, actions)
}

var __condToIf = (predicates, actions) => {
  if (predicates.length != 0 && predicates.length == actions.length) {
    var pred = predicates.shift()
    var action = actions.shift()
    if (pred == 'else') {
      return action
    } else {
      return new ASTNode('if', [pred, action, __condToIf(predicates, actions)])
    }
  }
}

var _makeIf = (pred, thenAction, elseAction) => {
  return new ASTNode('if', [pred, thenAction, elseAction])
}

var _isSequence = (ast) => {
  return Array.isArray(ast) && ast.length > 0
}

var _evalSequence = (ast, env) => {
  // todo: scan out possible definitions. if there is more than 0 defitions, turn the expression sequence into one let function and eval
  var output
  ast.forEach((_ast, i) => {
    var result = _eval(_ast, env)
    if (i == ast.length - 1) {
      output = result
    }
  })
  return output
}

var _sequenceToLet = (ast) => {
  var definitions = ast.filter(_ast => _ast.proc == 'define')
  var otherExprs = ast.filter(_ast => !(_ast.proc == 'define'))

  // convert (define (proc args) body) into (define name lambda) before further conversion
  definitions = definitions.map((ast) => {
    var name = ast.args[0]
    if (_isProcedure(name)) {
      return _defineProcToDefine(ast)
    } else {
      return ast
    }
  })

  var names = definitions.map(_ast => _ast.args[0])
  var values = definitions.map(_ast => _ast.args.slice(1))

  var bindingNodes = names.map(name => new ASTNode(name, 'undefined'))
  var firstBinding = bindingNodes.shift()
  var bindingPart = new ASTNode(firstBinding, bindingNodes)

  var setPart = names.map((name, i) => new ASTNode('set!', [name, values[i]]))
  var letBody = setPart.concat(otherExprs)

  var params = [bindingPart].concat(letBody)

  var result = new ASTNode('let', params)
  // todo: make sure the conversion sequence with definition => let => lambda is correct
  return new ASTNode('let', params)
}

var _isBegin = (ast) => {
  return ast.proc == 'begin'
}

var _evalBegin = (ast, env) => {
  var sequence = ast.args
  return _evalSequence(sequence, env)
}

var _sequenceToBegin = (ast) => {
  return new ASTNode('begin', ast)
}

var _isLambda = (ast) => {
  return ast.proc == 'lambda'
}

var _makeLambda = (ast, env) => {
  var params = ast.args[0]
  params = _astToArray(params)
  var body = ast.args.slice(1)
  return {
    params, body, env
  }
}

// for some part of the language, such as the parameter list of a lamda expression '(x y z)'
// the parsing algorithm might return a ast node unintended
// this function transform the ast node into an array with the proc as first element and args as remaining elements
var _astToArray = (ast) => {
  var arr = [ast.proc]
  if (ast.args && ast.args.length > 0) {
    arr = arr.concat(ast.args)
  }
  return arr
}

// setup
var _setupEnvironment = () => {
  var frame = new Frame(PRIMITIVES_PROCEDURES)
  var env = new Environment(null, frame)
  // PRIMITIVE_VALUES
  env.defineVariable('true', true)
  env.defineVariable('false', false)
  env.defineVariable('undefined', 'undefined')
  env.defineVariable('the-empty-list', theEmptyList)
  return env
}

var globalEnvironment = _setupEnvironment()

var code = `
(define (reduce proc init list)
  (if (null? list)
      init
      (reduce proc (proc init (car list)) (cdr list))))

(define (enum low high)
  (if (= low (+ high 1))
      the-empty-list
      (cons low (enum (+ low 1) high))))

(define (factorial n)
  (define (mult a b) (* a b))
  (define seq (enum 1 n))
  (reduce mult 1 seq))

(factorial 6)
`

var result = lisp_eval(code)
console.log(result)