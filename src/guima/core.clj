(ns guima.core
  (:require
   [io.pedestal.http :as http]
   [io.pedestal.http.body-params :as body-params]
   [io.pedestal.http.route :as route]
   [jsonista.core :as json]
   [clojure.set :as set]
   [clojure.java.io :as io]
   [guima.server.parser :as parser]
   [pathom.pedestal :refer [pathom-routes]])
  (:import
   (java.util Base64))
  (:gen-class))

(def editor
  [http/html-body
   {:enter
    (fn [context]
      (assoc context :response {:status 200
                                :body (slurp (io/resource "public/index.html"))}))}])

(def main-page
  [{:enter
    (fn [context]
      (assoc context
             :response {:status 302
                        :headers  {"location" "/editor"}}))}])

(def health-check
  [http/html-body
   {:enter
    (fn [context]
      (assoc context :response {:status 200 :body ""}))}])

(def pathom-api
  [{:enter
    (fn [context]
      (assoc context :response {:status 200 :body ""}))}])

(def routes
  (route/expand-routes
   (set/union
    #{["/" :get main-page :route-name :main-page]
      ["/editor" :get editor :route-name :editor]
      ["/health-check" :get health-check :route-name :health-check]}
    (pathom-routes {:pathom-viz? true :parser parser/pathom-parser :pathom-url "/api"}))))

(defn decode [to-decode]
  (String. (.decode (Base64/getDecoder) to-decode)))

;; Use `btoa` at javascript and `decode` here

(defn create-server [env]
  (http/create-server
   (-> {::http/routes routes
        ::http/type :jetty
        ::http/resource-path "/public"
        ::http/secure-headers nil
        ::http/allowed-origins (constantly true)
        ::http/host "0.0.0.0"
        #_{:creds true :allowed-origins (constantly true) #_#{"http://localhost:8080"
                                                              "http://localhost:4100"}}}
       (cond->
           (= env :dev) (assoc ::http/join? false
                               ::http/port 8080)
           (= env :prod) (assoc ::http/join? true
                                ::http/port 80))
       http/default-interceptors)))

(defn -main
  [& [env]]
  (let [server (create-server (keyword env))]
    (http/start server)))

;; create and start the server
(comment

  (def server nil)

  (do (some-> server http/stop)
      (def server (create-server :dev))
      (http/start server))

  ())
