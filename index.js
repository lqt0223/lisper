/* 
TODOLIST:
basic ok!
  tokenizing & parsing
  eval-apply metacircular model
  environment
the implementation of undefined
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

class Pair {
  constructor(head, tail) {
    this.head = head
    this.tail = tail
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
var theEmptyList = new Pair(null, null)
var cons = (a, b) => new Pair(a, b)
var car = (a) => a.head
var cdr = (a) => a.tail
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
  'null?': (a) => a && a.constructor && a.constructor.name == 'Pair' && a.head == null && a.tail == null,
  'cons': cons,
  'car': car,
  'cdr': cdr,
  'list': list,
}

for (var name in PRIMITIVES_PROCEDURES) {
  var proc = PRIMITIVES_PROCEDURES[name]
  proc.isPrimitive = true
}

var _lisp_eval = (ast, env) => {
  return _eval(ast, env)
}

// to evaluate, analyze the expression to form a expression ready to be executed, and execute in a given environment
var _eval = (ast, env) => {
  return _analyze(ast)(env)
}

var _analyze = (ast) => {
  if (_isNumber(ast)) {
    return _analyzeNumber(ast)
  } else if (_isString(ast)) {
    return _analyzeString(ast)
  } else if (_isVariable(ast)) {
    return _analyzeVariable(ast)
  } else if (_isAssign(ast)) {
    return _analyzeAssign(ast)
  } else if (_isDefine(ast)) {
    return _analyzeDefine(ast)
  } else if (_isLet(ast)) {
    return _analyze(_letToLambdaWithArgs(ast))
  } else if (_isIf(ast)) {
    return _analyzeIf(ast)
  } else if (_isCond(ast)) {
    return _analyze(_condToIf(ast))
  } else if (_isLambda(ast)) {
    return _analyzeLambda(ast)
  } else if (_isSequence(ast)) {
    return _analyzeSequence(ast)
  } else if (_isBegin(ast)) {
    return _analyzeBegin(ast)
  } else if (_isApply(ast)) {
    var proc = _analyze(ast.args[0])
    var args = _analyze(ast.args[1])
    return (env) => {
      return _apply(proc(env), _listToArr(args(env)))
    }
  // if its a procedure (a non-special expression)
  // evaluate its operator(proc) and operands(args), and do the application
  } else if (_isProcedure(ast)){
    var proc = _analyze(ast.proc)
    var args = ast.args.map((arg) => _analyze(arg))
    return (env) => {
      return _apply(proc(env), args.map(arg => arg(env)))
    }
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

var _analyzeVariable = (ast) => {
  return (env) => {
    return _lookUp(ast, env)
  }
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
// else, extend the environment of the procedure by creating bindings between formal parameters and actual arguments
// then analyze the procedure body to form a procedure ready to be executed
// finally execute it within the new environment
var _apply = (proc, args) => {
  if (_isPrimitive(proc)) {
    return _applyPrimitive(proc, args)
  } else {
    var bindings = _bind(proc.params, args)
    var frame = new Frame(bindings)
    var newEnv = proc.env.extend(frame)
    return _analyze(proc.body)(newEnv)
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
  return /^[0-9.]+$/.test(ast) && ast.split('.').length <= 2
}

var _analyzeNumber = (ast) => {
  return (env) => {
    if (ast.split('.').length == 2) {
      return parseFloat(ast)
    } else {
      return parseInt(ast)
    }
  }
}

var _isString = (ast) => {
  return ast[0] == '`'
}

var _analyzeString = (ast) => {
  return (env) => {
    return ast.slice(1)
  }
}

// transform list (nested-pair) into an one-dimensional array
var _listToArr = (list) => {
  var arr = []
  var result =  __listToArr(list, arr)
  return result
}

var __listToArr = (list, arr) => {
  if (list.head == null && list.tail == null) {
    return arr
  } else {
    arr.push(list.head)
    return __listToArr(list.tail, arr)
  }
}

var _isDefine = (ast) => {
  return ast.proc == 'define'
}

var _analyzeDefine = (ast) => {
  var name = ast.args[0]
  // to support the (define (procName procParams) (procBody)) syntatic sugar
  if (_isProcedure(name)) {
    ast = _defineProcToDefine(ast)
    name = ast.args[0]
  }
  var value = _analyze(ast.args[1])
  return (env) => {
    env.defineVariable(name, value(env))
    return 'define ok'
  }
}

var _defineProcToDefine = (ast) => {
  var procName = ast.args[0].proc
  var procParams = ast.args[0].args
  var procBody = ast.args.slice(1)

  var firstParam = procParams.shift()
  var paramNode = new ASTNode(firstParam, procParams)
  var lambdaNode = new ASTNode('lambda', [paramNode, procBody])
  return new ASTNode('define', [procName, lambdaNode])
}

var _isAssign = (ast) => {
  return ast.proc == 'set!'
}

var _analyzeAssign = (ast) => {
  var name = ast.args[0]
  var value = _analyze(ast.args[1])
  return (env) => {
    env.set(name, value(env))
    return `set ${name} ${value(env)} ok!`
  }
}

var _isLet = (ast) => {
  return ast.proc == 'let'
}

var _letToLambdaWithArgs = (ast, env) => {
  var firstArg = ast.args[0].proc.args[0]
  var restArgs = ast.args[0].args
  if (restArgs && restArgs.length > 0) {
    restArgs = restArgs.map(_ast => _ast.args[0])
  } else {
    restArgs = []
  }

  var args = [firstArg]
  if (restArgs && restArgs.length != 0) {
    args = args.concat(restArgs)
  }

  var lambda = _letToLambda(ast)
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

var _analyzeIf = (ast) => {
  var pred = _analyze(ast.args[0])
  var thenAction = _analyze(ast.args[1])
  var elseAction = _analyze(ast.args[2])
  return (env) => {
    if (pred(env)) {
      return thenAction(env)
    } else {
      return elseAction(env)
    }
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

var _isSequence = (ast) => {
  return Array.isArray(ast) && ast.length > 0
}

var _analyzeSequence = (ast) => {
  var definitions = ast.filter((_ast) => _ast.proc == 'define')
  var nonDefinitions = ast.filter((_ast) => !(_ast.proc == 'define'))

  if (definitions.length > 0) {
    ast = _sequenceToLet(ast)
    return (env) => {
      return _analyze(ast)(env)
    }
  } else {
    var output
    var analyzedSequence = ast.map(_analyze)
    return (env) => {
      analyzedSequence.forEach((analyzed) => {
        output = analyzed(env)
      })
      return output
    }
  }
}

var _sequenceToLet = (ast) => {
  var definitions = ast.filter(_ast => _ast.proc == 'define')
  var nonDefinitions = ast.filter(_ast => !(_ast.proc == 'define'))

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
  var values = definitions.map(_ast => _ast.args[1])

  var bindingNodes = names.map(name => new ASTNode(name, ['undefined']))
  var firstBinding = bindingNodes.shift()
  var bindingPart = new ASTNode(firstBinding, bindingNodes)

  var setPart = names.map((name, i) => new ASTNode('set!', [name, values[i]]))
  var letBody = setPart.concat(nonDefinitions)
  var params = [bindingPart].concat(letBody)

  return new ASTNode('let', params)
}

var _isBegin = (ast) => {
  return ast.proc == 'begin'
}

var _analyzeBegin = (ast) => {
  var sequence = ast.args
  return _analyzeSequence(sequence)
}

var _sequenceToBegin = (ast) => {
  return new ASTNode('begin', ast)
}

var _isLambda = (ast) => {
  return ast.proc == 'lambda'
}

var _analyzeLambda = (ast) => {
  return (env) => {
    return _makeProcedure(ast, env)
  }
}

var _makeProcedure = (ast, env) => {
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
  (define args (list mult 1 seq))
  (apply reduce args))

(factorial 6)
`

var result = lisp_eval(code)
console.log(result)