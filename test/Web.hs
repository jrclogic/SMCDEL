{-# LANGUAGE OverloadedStrings#-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import System.Process (withCreateProcess, proc)
import Test.Sandwich
import Test.Sandwich.WebDriver
import Test.WebDriver

spec :: TopSpec
spec = introduceWebDriver wdOptions $ do
  it "MuddyChildren example yields expected result" $ withSession1 $ do
    openPage "http://127.0.0.1:3000/index.html"
    findElem (ByCSS "input[value='MuddyChildren']") >>= click
    findElem (ByCSS "#runbutton") >>= click
    liftIO $ threadDelay 3000000 -- longer wait for MathJax
    output <- getText =<< findElem (ByCSS "#output")
    output `textShouldContain` "Oalice={p2,p3}"
    output `textShouldContain` expectedMcOutput
  it "Empty input yields a parse error" $ withSession1 $ do
    openPage "http://127.0.0.1:3000/index.html"
    findElem (ByCSS "#runbutton") >>= click
    liftIO $ threadDelay 1000000
    output <- getText =<< findElem (ByCSS "#output")
    output `textShouldContain` "Parse error in line 1, column 1"
  it "Unknown symbols yield lexing error" $ withSession1 $ do
    openPage "http://127.0.0.1:3000/index.html"
    findElem (ByCSS ".ace_text-input") >>= clearInput
    findElem (ByCSS ".ace_text-input") >>= sendKeys "@ $ %"
    findElem (ByCSS "#runbutton") >>= click
    liftIO $ threadDelay 1000000
    output <- getText =<< findElem (ByCSS "#output")
    output `textShouldContain` "Lex error"
  it "Formula with unknown agent yields sanity error" $ withSession1 $ do
    openPage "http://127.0.0.1:3000/index.html"
    findElem (ByCSS ".ace_text-input") >>= clearInput
    findElem (ByCSS ".ace_text-input") >>= sendKeys wrongAgentInput
    findElem (ByCSS "#runbutton") >>= click
    liftIO $ threadDelay 1000000
    output <- getText =<< findElem (ByCSS "#output")
    output `textShouldContain` "Sanity error: Query formula contains agents not in OBS"

expectedMcOutput :: Text
expectedMcOutput = "At which states is\n⟨!⋁{p1,p2,p3}⟩⋁{Kalice?p1,Kbob?p2,Kcarol?p3}\ntrue?\n{p1},{p2},{p3}\n"

wrongAgentInput :: Text
wrongAgentInput = "VARS 1,2 LAW Top OBS alice: 1 bob: 2 WHERE? charlie knows that 1"

wdOptions :: WdOptions
wdOptions = (defaultWdOptions "/tmp/tools") {
  capabilities = firefoxCapabilities Nothing
  , runMode = RunHeadless defaultHeadlessConfig
  }

main :: IO ()
main = do
  withCreateProcess (proc "stack" ["exec", "smcdel-web"]) $
    \_ _ _ _ -> do
      (_, numFailures) <- runSandwich' Nothing defaultOptions spec
      when (numFailures > 0) $ error $ show numFailures ++ " tests failed"
