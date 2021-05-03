/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.dubbo.rpc.cluster.filter;

import org.apache.dubbo.common.URL;
import org.apache.dubbo.common.extension.SPI;
import org.apache.dubbo.rpc.BaseFilter;
import org.apache.dubbo.rpc.Filter;
import org.apache.dubbo.rpc.Invocation;
import org.apache.dubbo.rpc.Invoker;
import org.apache.dubbo.rpc.ListenableFilter;
import org.apache.dubbo.rpc.LoopFilter;
import org.apache.dubbo.rpc.Result;
import org.apache.dubbo.rpc.RpcException;
import org.apache.dubbo.rpc.cluster.ClusterInvoker;
import org.apache.dubbo.rpc.cluster.Directory;

import java.util.ArrayList;
import java.util.List;

@SPI("default")
public interface FilterChainBuilder {
    /**
     * build consumer/provider filter chain
     */
    <T> Invoker<T> buildInvokerChain(final Invoker<T> invoker, String key, String group);

    /**
     * build consumer cluster filter chain
     */
    <T> ClusterInvoker<T> buildClusterInvokerChain(final ClusterInvoker<T> invoker, String key, String group);

    /**
     * Works on provider side
     *
     * @param <T>
     * @param <TYPE>
     */
    class FilterChainNode<T, TYPE extends Invoker<T>, FILTER extends BaseFilter> implements Invoker<T> {
        TYPE originalInvoker;
        Invoker<T> nextNode;
        FILTER filter;

        public FilterChainNode(TYPE originalInvoker, Invoker<T> nextNode, FILTER filter) {
            this.originalInvoker = originalInvoker;
            this.nextNode = nextNode;
            this.filter = filter;
        }

        public TYPE getOriginalInvoker() {
            return originalInvoker;
        }

        @Override
        public Class<T> getInterface() {
            return originalInvoker.getInterface();
        }

        @Override
        public URL getUrl() {
            return originalInvoker.getUrl();
        }

        @Override
        public boolean isAvailable() {
            return originalInvoker.isAvailable();
        }

        @Override
        public Result invoke(Invocation invocation) throws RpcException {
            Result asyncResult;
            try {
                asyncResult = filter.invoke(nextNode, invocation);
            } catch (Exception e) {
                if (filter instanceof ListenableFilter) {
                    ListenableFilter listenableFilter = ((ListenableFilter) filter);
                    try {
                        Filter.Listener listener = listenableFilter.listener(invocation);
                        if (listener != null) {
                            listener.onError(e, originalInvoker, invocation);
                        }
                    } finally {
                        listenableFilter.removeListener(invocation);
                    }
                } else if (filter instanceof FILTER.Listener) {
                    FILTER.Listener listener = (FILTER.Listener) filter;
                    listener.onError(e, originalInvoker, invocation);
                }
                throw e;
            } finally {

            }
            return asyncResult.whenCompleteWithContext((r, t) -> {
                if (filter instanceof ListenableFilter) {
                    ListenableFilter listenableFilter = ((ListenableFilter) filter);
                    Filter.Listener listener = listenableFilter.listener(invocation);
                    try {
                        if (listener != null) {
                            if (t == null) {
                                listener.onResponse(r, originalInvoker, invocation);
                            } else {
                                listener.onError(t, originalInvoker, invocation);
                            }
                        }
                    } finally {
                        listenableFilter.removeListener(invocation);
                    }
                } else if (filter instanceof FILTER.Listener) {
                    FILTER.Listener listener = (FILTER.Listener) filter;
                    if (t == null) {
                        listener.onResponse(r, originalInvoker, invocation);
                    } else {
                        listener.onError(t, originalInvoker, invocation);
                    }
                }
            });
        }

        @Override
        public void destroy() {
            originalInvoker.destroy();
        }

        @Override
        public String toString() {
            return originalInvoker.toString();
        }
    }


    /**
     * Works on provider side
     *
     * @param <T>
     * @param <TYPE>
     */
    class LoopFilterChainNode<T, TYPE extends Invoker<T>, LOOP_FILTER extends LoopFilter> implements Invoker<T> {
        TYPE originalInvoker;
        Invoker<T> nextNode;
        List<LOOP_FILTER> filterList;

        public LoopFilterChainNode(TYPE originalInvoker, Invoker<T> nextNode, LOOP_FILTER loopFilter) {
            this.originalInvoker = originalInvoker;
            this.nextNode = nextNode;
            this.filterList = new ArrayList<>();
            this.filterList.add(loopFilter);
        }

        public void addLoopFilter(LOOP_FILTER loopFilter) {
            filterList.add(0, loopFilter);
        }

        public TYPE getOriginalInvoker() {
            return originalInvoker;
        }

        @Override
        public Class<T> getInterface() {
            return originalInvoker.getInterface();
        }

        @Override
        public URL getUrl() {
            return originalInvoker.getUrl();
        }

        @Override
        public boolean isAvailable() {
            return originalInvoker.isAvailable();
        }

        @Override
        public Result invoke(Invocation invocation) throws RpcException {
            Result asyncResult = null;
            int currentDepth = 0;
            try {
                for (currentDepth = 0; currentDepth < filterList.size(); currentDepth++) {
                    LOOP_FILTER filter = filterList.get(currentDepth);
                    asyncResult = filter.onBefore(nextNode, invocation);
                    if (asyncResult != null) {
                        break;
                    }
                }
                currentDepth--;
                asyncResult = nextNode.invoke(invocation);
                for (; currentDepth >= 0; currentDepth--) {
                    LOOP_FILTER filter = filterList.get(currentDepth);
                    asyncResult = filter.onAfter(nextNode, invocation, asyncResult);
                }
            } catch (Exception e) {
                for (; currentDepth >= 0; currentDepth--) {
                    LOOP_FILTER filter = filterList.get(currentDepth);
                    try {
                        if (filter instanceof ListenableFilter) {
                            ListenableFilter listenableFilter = ((ListenableFilter) filter);
                            try {
                                Filter.Listener listener = listenableFilter.listener(invocation);
                                if (listener != null) {
                                    listener.onError(e, originalInvoker, invocation);
                                }
                            } finally {
                                listenableFilter.removeListener(invocation);
                            }
                        } else if (filter instanceof Filter.Listener) {
                            Filter.Listener listener = (Filter.Listener) filter;
                            listener.onError(e, originalInvoker, invocation);
                        }
                    } finally {
                        filter.onAfter(nextNode, invocation, null);
                    }
                }
                throw e;
            }
            return asyncResult.whenCompleteWithContext((r, t) -> {
                for (int i = filterList.size() - 1; i >= 0; i--) {
                    LOOP_FILTER filter = filterList.get(i);
                    if (filter instanceof ListenableFilter) {
                        ListenableFilter listenableFilter = ((ListenableFilter) filter);
                        Filter.Listener listener = listenableFilter.listener(invocation);
                        try {
                            if (listener != null) {
                                if (t == null) {
                                    listener.onResponse(r, originalInvoker, invocation);
                                } else {
                                    listener.onError(t, originalInvoker, invocation);
                                }
                            }
                        } finally {
                            listenableFilter.removeListener(invocation);
                        }
                    } else if (filter instanceof Filter.Listener) {
                        Filter.Listener listener = (Filter.Listener) filter;
                        if (t == null) {
                            listener.onResponse(r, originalInvoker, invocation);
                        } else {
                            listener.onError(t, originalInvoker, invocation);
                        }
                    }
                }
            });
        }

        @Override
        public void destroy() {
            originalInvoker.destroy();
        }

        @Override
        public String toString() {
            return originalInvoker.toString();
        }
    }

    /**
     * Works on consumer side
     *
     * @param <T>
     * @param <TYPE>
     */
    class ClusterFilterChainNode<T, TYPE extends ClusterInvoker<T>, FILTER extends BaseFilter>
            extends FilterChainNode<T, TYPE, FILTER> implements ClusterInvoker<T> {
        public ClusterFilterChainNode(TYPE originalInvoker, Invoker<T> nextNode, FILTER filter) {
            super(originalInvoker, nextNode, filter);
        }


        @Override
        public URL getRegistryUrl() {
            return getOriginalInvoker().getRegistryUrl();
        }

        @Override
        public Directory<T> getDirectory() {
            return getOriginalInvoker().getDirectory();
        }

        @Override
        public boolean isDestroyed() {
            return getOriginalInvoker().isDestroyed();
        }
    }
}
