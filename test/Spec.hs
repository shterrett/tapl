import Control.Monad (void)
import qualified Arithmetic.InterpreterSpec as Arith
import qualified LambdaCalc.UntypedSpec as ULC
import qualified LambdaCalc.SimplyTypedSpec as STLC
import qualified LambdaCalc.SubtypingSpec as SBTY
import qualified SystemF.TypeCheckerSpec as SF
import Test.HUnit (runTestTT, Test(..))

main :: IO ()
main = void . runTestTT . TestList $
    [ Arith.tests
    , ULC.tests
    , STLC.tests
    , SBTY.tests
    , SF.tests
    ]
