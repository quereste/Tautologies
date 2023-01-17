data Symbol = P | Q | OR | AND | NOT | THEN | IFF | LEFT | RIGHT deriving (Eq, Show)
data Result = Zero | One deriving (Show, Eq)

tautologies :: Int -> [String]

tautologies n = [prettyPrint x | x <- (generateAllStrings n), checkBrackets x, fixStuff x, checkTruth (convertInfixPostfix x)]

convertInfixPostfix :: [Symbol] -> [Symbol]
convertInfixPostfix arr = convertInfixPostfix' arr [] []

convertInfixPostfix' :: [Symbol] -> [Symbol] -> [Symbol] -> [Symbol]
convertInfixPostfix' [] [] result = reverse result
convertInfixPostfix' [] (s:stack) result = convertInfixPostfix' [] stack (s:result)
convertInfixPostfix' (P:args) stack result = convertInfixPostfix' args stack (P:result)
convertInfixPostfix' (Q:args) stack result = convertInfixPostfix' args stack (Q:result)
convertInfixPostfix' (LEFT:args) stack result = convertInfixPostfix' args (LEFT:stack) result
convertInfixPostfix' (RIGHT:args) (LEFT:stack) result = convertInfixPostfix' args stack result
convertInfixPostfix' (RIGHT:args) (x:stack) result = convertInfixPostfix' (RIGHT:args) stack (x:result)
convertInfixPostfix' (op:args) [] result = convertInfixPostfix' args [op] result
convertInfixPostfix' (op:args) (LEFT:stack) result = convertInfixPostfix' args (op:LEFT:stack) result
convertInfixPostfix' (op:args) (s:stack) result = if (precedence op) <= (precedence s) then
  convertInfixPostfix' (op:args) stack (s:result) else
  convertInfixPostfix' args (op:s:stack) result

precedence :: Symbol -> Int
precedence NOT = 4
precedence AND = 3
precedence OR = 2
precedence THEN = 1
precedence IFF = 0

symbols = [P, Q, OR, AND, NOT, THEN, IFF, LEFT, RIGHT]
numberOfSymbols = 9

checkBrackets :: [Symbol] -> Bool
checkBrackets arr = checkBrackets' arr 0 False

checkBrackets' :: [Symbol] -> Int -> Bool -> Bool

checkBrackets' [] n _ = if n == 0 then True else False
checkBrackets' (LEFT:xs) n c = checkBrackets' xs (n + 1) True
checkBrackets' (RIGHT:xs) n c = if c then False else 
  if n == 0 then False else checkBrackets' xs (n - 1) False
checkBrackets' (_:xs) n _ = checkBrackets' xs n False

extractBracket :: [Symbol] -> ([Symbol], [Symbol])
extractBracket arr = extractBracket' arr [] 1

extractBracket' :: [Symbol] -> [Symbol] -> Int -> ([Symbol], [Symbol])
extractBracket' (LEFT:xs) rest n = extractBracket' xs (LEFT:rest) (n+1)
extractBracket' (RIGHT:xs) rest n = if n == 1 then (xs, reverse rest) else extractBracket' xs (RIGHT:xs) (n - 1) 
extractBracket' (x:xs) rest n = extractBracket' xs (x:rest) n 
data Mode = Token | Op | Not | None deriving Eq

fixStuff :: [Symbol] -> Bool
fixStuff arr = fixStuff' arr None

fixStuff' :: [Symbol] -> Mode -> Bool
fixStuff' [] Token = True
fixStuff' [] _ = False
fixStuff' (x:xs) t
  | x == P && t == Token = False
  | x == Q && t == Token = False
  | x == P && t == None = fixStuff' xs Token
  | x == Q && t == None = fixStuff' xs Token
  | x == P || x == Q = fixStuff' xs Token
  | x == LEFT && t == Token = False
  | x == LEFT = if fixStuff' partOne None  then if partTwo == [] then True else fixStuff' partTwo Token else False
  | x == NOT && t == Token = False
  | x == NOT = fixStuff' xs Not
  | t == Op = False
  | t == Not = fixStuff' xs Not
  | t == Token = fixStuff' xs Op
  | t == None = False 
  where (partTwo, partOne) = extractBracket xs

generateAllStrings :: Int -> [[Symbol]]
generateAllStrings n = generateAllStringsInner 0 n []

generateAllStringsInner :: Int -> Int -> [[Symbol]] -> [[Symbol]]

generateAllStringsInner _ 0 _ = []
generateAllStringsInner 0 1 _ = [[P], [Q], [OR], [AND], [NOT], [THEN], [IFF], [LEFT], [RIGHT]]

generateAllStringsInner 0 n _ = (generateAllStringsInner 0 1 []) ++ generateAllStringsInner 1 n [[P], [Q], [OR], [AND], [NOT], [THEN], [IFF], [LEFT], [RIGHT]]


generateAllStringsInner i n material = if i == n then []
  else result ++ (generateAllStringsInner (i + 1) n result) where result = appendEverySymbol material

appendEverySymbol :: [[Symbol]] -> [[Symbol]]

appendEverySymbol [] = []
appendEverySymbol (x:xs) = (myZip symbols (replicate numberOfSymbols x)) ++  appendEverySymbol xs

myZip :: [Symbol] -> [[Symbol]] -> [[Symbol]]

myZip [] [] = []
myZip (x:xs) (y:ys) = (x:y) : myZip xs ys


prettyPrint :: [Symbol] -> String
prettyPrint [] = ""
prettyPrint (x:xs) = (printSymbol x) ++ (prettyPrint xs)

printSymbol :: Symbol -> String
printSymbol x 
 | x == P = "P"
 | x == Q = "Q"
 | x == OR = "||"
 | x == AND = "&&"
 | x == NOT = "~"
 | x == THEN = "=>"
 | x == IFF = "<=>"
 | x == LEFT = "("
 | x == RIGHT = ")"

checkTruth :: [Symbol] -> Bool
checkTruth x = if (evaluateONP x [] evaluateVar10 == One 
  && evaluateONP x [] evaluateVar11 == One
  && evaluateONP x [] evaluateVar01 == One
  && evaluateONP x [] evaluateVar00 == One) then True else False 

evaluateVar10 :: Symbol -> Result
evaluateVar10 P = One
evaluateVar10 Q = Zero

evaluateVar11 :: Symbol -> Result
evaluateVar11 P = One
evaluateVar11 Q = One

evaluateVar01 :: Symbol -> Result
evaluateVar01 P = Zero
evaluateVar01 Q = One

evaluateVar00 :: Symbol -> Result
evaluateVar00 P = Zero
evaluateVar00 Q = Zero

evaluateONP :: [Symbol] -> [Result] -> (Symbol -> Result) -> Result

evaluateONP [] (x:[]) f = x

evaluateONP (P:rest) xs f = evaluateONP rest (eval:xs) f where
  eval = f P

evaluateONP (Q:rest) xs f = evaluateONP rest (eval:xs) f where
  eval = f Q

evaluateONP (NOT:rest) (x:xs) f = evaluateONP rest (eval:xs) f
  where eval = negation x
 
evaluateONP (s:rest) (x:y:xs) f
  | s == OR = evaluateONP rest ((alternative y x):xs) f
  | s == AND = evaluateONP rest ((conjunction y x):xs) f
  | s == IFF = evaluateONP rest ((equivalence y x):xs) f
  | s == THEN = evaluateONP rest ((implication y x):xs) f

evaluateONP _ _ _ = Zero

negation :: Result -> Result
negation r = if r == Zero then One else Zero

conjunction :: Result -> Result -> Result
conjunction rOne rTwo = if rOne == One && rTwo == One then One else Zero   

alternative :: Result -> Result -> Result
alternative rOne rTwo = if rOne == Zero && rTwo == Zero then Zero else One

implication :: Result -> Result -> Result
implication rOne rTwo = if rOne == One && rTwo == Zero then Zero else One

equivalence :: Result -> Result -> Result
equivalence rOne rTwo = if rOne == rTwo then One else Zero
