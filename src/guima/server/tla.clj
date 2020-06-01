(ns guima.server.tla
  (:require
   [clojure.java.shell :as sh]
   [clojure.string :as str]))

;; From http://makble.com/clojure-regular-expression-extract-text-between-two-strings
(defn make-literal [a]
  (.replace a "\"" "\\\""))

(defn- extract-anything-between [prefix suffix from-string]
  (let [pattern (str (make-literal prefix) "([\\s\\S]*?)" (make-literal suffix))]
    (second (re-find (re-pattern pattern) from-string))))

(def ^:private spec-template
  "
----------------------------- MODULE %s -----------------------------
EXTENDS Naturals, Sequences, IOUtils, FiniteSets, TLC
%s
Init == /\\ PrintT(\"TLAREPL_START\")
        /\\ PrintT(ToString(%s))
        /\\ PrintT(\"TLAREPL_END\")
        /\\ TRUE

Next == TRUE
Spec == Init
=================================================================================
")

(defn- run-repl
  [spec]
  (sh/with-sh-env {"PLUSPYPATH"
                   ".:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other:/tmp"}
    (sh/sh "python3" "PlusPy/pluspy.py" "-c2" spec)))

(defn- eval-tla
  [ctx expr]
  (let [{:keys [:out :exit] :as response}
        (let [spec-file (java.io.File/createTempFile "TLAWebREPL" ".tla")
              spec-name (-> (.getName spec-file) (str/split #"\.") first)]
          (println (.getAbsolutePath spec-file))
          (spit spec-file (format spec-template spec-name ctx expr))
          (run-repl spec-name))]
    (clojure.pprint/pprint {:v response})
    (if-not (zero? exit)
      (throw
       (ex-info "Error evaluating spec" response))
      (if (re-find #"TLAREPL_START" out)
        (->> out
             (extract-anything-between "TLAREPL_START" "TLAREPL_END")
             (#(subs % 1 (dec (count %)))))
        (do (print out)
            out)))))

(defn eval-tla-expression
  [input]
  (let [
        ;; append new line so it can parse more easily later
        input-lines (->> (str/split input #"----+")
                         (mapcat #(->> (str/split % #"\(\*([^\)]+)\*\)")
                                       (remove empty?)
                                       (map str/trim)))
                         seq)
        [expr-context expr] (cond
                              (= (count input-lines) 2)
                              (if (empty? (last input-lines))
                                [(first input-lines) "\"\""]
                                input-lines)

                              (= (count input-lines) 1)
                              (if (empty? (last input-lines))
                                ["" "\"\""]
                                (cons "" input-lines))

                              :else ["" "\"\""])]
    (try
      {:data (eval-tla expr-context expr)}
      (catch Exception e {:error {:message (:out (ex-data e))}}))))

(comment

  ;; Working section -------------------
  (eval-tla "" "3 + 5")

  (eval-tla "" "<<4, 5, 5>> \\o <<10>>")

  (eval-tla "" "60 \\div 7")

  (eval-tla (->> [
                  "IndexOf(seq, elem) == CHOOSE i \\in 1..Len(seq): seq[i] = elem"]
                 (str/join "\n"))
            "IndexOf(<<3, 6, 7>>, 3)")

  (eval-tla "" "1 \\in {3, 4, 1}")

  (eval-tla "" "Len(<<3, 2>>)")

  (eval-tla "" "Head(<<3, 2>>)")

  (eval-tla "" "Tail(<<4, 12>>)")

  (eval-tla "" "{1, 2} \\subseteq {1, 2, 3}")

  (eval-tla "" "Cardinality({3})")

  (eval-tla "" "{2, 3} \\cup {50, 2}")

  ())
