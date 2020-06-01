(ns guima.server.parser
  (:require
   [com.wsscode.pathom.core :as p]
   [guima.handler.mutation :as mutation]
   [guima.server.resolver :as resolver]
   [com.wsscode.pathom.connect :as pc]))

(def resolvers [resolver/resolvers mutation/mutations])

(def pathom-parser
  (p/parser {::p/env     {::p/reader                 [p/map-reader
                                                      pc/reader2
                                                      pc/ident-reader
                                                      pc/index-reader]
                          ::pc/mutation-join-globals [:tempids]}
             ::p/mutate  pc/mutate
             ::p/plugins [(pc/connect-plugin {::pc/register resolvers})
                          p/error-handler-plugin]}))
