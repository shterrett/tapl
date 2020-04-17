import Control.Monad (void)
import Arithmetic.InterpreterSpec (tests)
import Test.HUnit (runTestTT)

main :: IO ()
main = void $ runTestTT tests
