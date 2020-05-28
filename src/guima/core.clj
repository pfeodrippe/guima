(ns guima.core
  (:require
   [clojure.java.shell :as sh]
   [clojure.string :as str]
   [io.pedestal.http :as http]
   [io.pedestal.http.body-params :as body-params]
   [io.pedestal.http.route :as route]
   [jsonista.core :as json]
   [clojure.set :as set]
   [clojure.java.io :as io])
  (:gen-class))

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

(def eval-tla-expression
  [(body-params/body-params)
   {:enter
    (fn [{:keys [:request] :as context}]
      (let [
            ;; append new line so it can parse more easily later
            input (str (get-in request [:json-params :input]) "\n")
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
        (assoc context :response
               (try
                 {:status 200
                  :body (json/write-value-as-string
                         {:data (eval-tla expr-context expr)})}
                 (catch Exception e
                   {:status 400
                    :body (json/write-value-as-string
                           {:error {:message (:out (ex-data e))}})})))))}])

(def main-page
  [http/html-body
   {:enter
    (fn [context]
      (assoc context :response {:status 200
                                :body (slurp (io/resource "public/index.html"))}))}])

(def routes
  (route/expand-routes
   #{["/" :get main-page :route-name :main-page]
     ["/eval-tla-expression" :post eval-tla-expression :route-name :eval-tla-expression]}))

(defn create-server [env]
  (http/create-server
   (-> {::http/routes routes
        ::http/type :jetty
        ::http/port 8080
        ::http/resource-path "/public"
        ::http/secure-headers nil
        ::http/allowed-origins (constantly true)
        #_{:creds true :allowed-origins (constantly true) #_#{"http://localhost:8080"
                                                              "http://localhost:4100"}}}
       (cond-> (= env :dev) (assoc ::http/join false))
       http/default-interceptors)))

(defn -main
  [& [env]]
  (let [server (create-server (keyword env))]
    (http/start server)))

;; create and start the server
(comment

  (do (def server (create-server))
      (http/start server))

  (http/stop server)

  ())
