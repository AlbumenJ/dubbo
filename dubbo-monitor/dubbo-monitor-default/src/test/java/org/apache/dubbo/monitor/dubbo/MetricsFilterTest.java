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
package org.apache.dubbo.monitor.dubbo;

import org.apache.dubbo.common.URL;
import org.apache.dubbo.common.utils.NetUtils;
import org.apache.dubbo.monitor.MetricsService;
import org.apache.dubbo.monitor.dubbo.service.DemoService;
import org.apache.dubbo.rpc.AppResponse;
import org.apache.dubbo.rpc.AsyncRpcResult;
import org.apache.dubbo.rpc.Invocation;
import org.apache.dubbo.rpc.Invoker;
import org.apache.dubbo.rpc.Protocol;
import org.apache.dubbo.rpc.RpcContext;
import org.apache.dubbo.rpc.RpcException;
import org.apache.dubbo.rpc.RpcInvocation;
import org.apache.dubbo.rpc.cluster.filter.FilterChainBuilder;
import org.apache.dubbo.rpc.protocol.dubbo.DubboProtocol;

import com.alibaba.metrics.FastCompass;
import com.alibaba.metrics.IMetricManager;
import com.alibaba.metrics.MetricLevel;
import com.alibaba.metrics.MetricManager;
import com.alibaba.metrics.MetricName;
import com.alibaba.metrics.common.MetricObject;
import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.apache.dubbo.common.constants.CommonConstants.CONSUMER_SIDE;
import static org.apache.dubbo.common.constants.CommonConstants.PROVIDER;
import static org.apache.dubbo.common.constants.CommonConstants.SIDE_KEY;
import static org.apache.dubbo.common.constants.CommonConstants.TIMEOUT_KEY;
import static org.apache.dubbo.monitor.Constants.DUBBO_CONSUMER;
import static org.apache.dubbo.monitor.Constants.DUBBO_CONSUMER_METHOD;
import static org.apache.dubbo.monitor.Constants.DUBBO_GROUP;
import static org.apache.dubbo.monitor.Constants.DUBBO_PROVIDER;
import static org.apache.dubbo.monitor.Constants.DUBBO_PROVIDER_METHOD;
import static org.apache.dubbo.monitor.Constants.METHOD;
import static org.apache.dubbo.monitor.Constants.SERVICE;
import static org.mockito.BDDMockito.given;
import static org.mockito.Mockito.doNothing;
import static org.mockito.Mockito.mock;

public class MetricsFilterTest {

    private final Function<URL, Invoker<DemoService>> invokerFunction = (url)-> {
        Invoker<DemoService> serviceInvoker = mock(Invoker.class);

        given(serviceInvoker.isAvailable()).willReturn(false);
        given(serviceInvoker.getInterface()).willReturn(DemoService.class);
        given(serviceInvoker.getUrl()).willReturn(url);
        given(serviceInvoker.invoke(Mockito.any(Invocation.class))).willReturn(null);
        doNothing().when(serviceInvoker).destroy();
        return serviceInvoker;
    };

    private URL getUrl() {
        return URL.valueOf("dubbo://" + NetUtils.getLocalHost() + ":20880/org.apache.dubbo.monitor.dubbo.service.DemoService");
    }

    private void onInvokeReturns(Invoker<DemoService> invoker, AppResponse response) {
        given(invoker.invoke(Mockito.any(Invocation.class))).willReturn(response);
    }

    public void onInvokerThrows(Invoker<DemoService> invoker) {
        given(invoker.invoke(Mockito.any(Invocation.class))).willThrow(new RpcException(RpcException.TIMEOUT_EXCEPTION));
    }

    @Test
    public void testConsumerSuccess() throws Exception {
        IMetricManager metricManager = MetricManager.getIMetricManager();
        metricManager.clear();
        MetricsFilter metricsFilter = new MetricsFilter();
        Invocation invocation = new RpcInvocation("sayName", DemoService.class.getName(), "", new Class<?>[]{Integer.class}, new Object[0]);
        RpcContext.getServiceContext().setRemoteAddress(NetUtils.getLocalHost(), 20880).setLocalAddress(NetUtils.getLocalHost(), 2345);
        URL url = getUrl().addParameter(SIDE_KEY, CONSUMER_SIDE);
        Invoker<DemoService> invoker = invokerFunction.apply(url);
        given(invoker.invoke(Mockito.any(Invocation.class))).willAnswer((invocation1)->AsyncRpcResult.newDefaultAsyncResult(1 ,(Invocation) invocation1.getArgument(0)));

        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> serviceInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(invoker, invoker, metricsFilter);

        for (int i = 0; i < 100; i++) {
            serviceInvokerNode.invoke(invocation);
        }
        FastCompass dubboClient = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_CONSUMER, MetricLevel.MAJOR));
        FastCompass dubboMethod = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_CONSUMER_METHOD, new HashMap<String, String>(4) {
            {
                put(SERVICE, "org.apache.dubbo.monitor.dubbo.service.DemoService");
                put(METHOD, "void sayName(Integer)");
            }
        }, MetricLevel.NORMAL));
        long timestamp = System.currentTimeMillis() / 5000 * 5000;
        Assertions.assertEquals(100, dubboClient.getMethodCountPerCategory(0).get("success").get(timestamp));
        timestamp = timestamp / 15000 * 15000;
        Assertions.assertEquals(100, dubboMethod.getMethodCountPerCategory(0).get("success").get(timestamp));

    }

    @Test
    public void testConsumerTimeout() {
        IMetricManager metricManager = MetricManager.getIMetricManager();
        metricManager.clear();
        MetricsFilter metricsFilter = new MetricsFilter();
        Invocation invocation = new RpcInvocation("timeoutException", DemoService.class.getName(), "", null, null);
        RpcContext.getServiceContext().setRemoteAddress(NetUtils.getLocalHost(), 20880).setLocalAddress(NetUtils.getLocalHost(), 2345);
        URL url = getUrl().addParameter(SIDE_KEY, CONSUMER_SIDE)
                .addParameter(TIMEOUT_KEY, 300);
        Invoker<DemoService> invoker = invokerFunction.apply(url);
        onInvokerThrows(invoker);

        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> serviceInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(invoker, invoker, metricsFilter);

        for (int i = 0; i < 10; i++) {
            try {
                serviceInvokerNode.invoke(invocation);
            } catch (RpcException e) {
                //ignore
            }
        }
        FastCompass dubboClient = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_CONSUMER, MetricLevel.MAJOR));
        FastCompass dubboMethod = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_CONSUMER_METHOD, new HashMap<String, String>(4) {
            {
                put(SERVICE, "org.apache.dubbo.monitor.dubbo.service.DemoService");
                put(METHOD, "void timeoutException()");
            }
        }, MetricLevel.NORMAL));
        long timestamp = System.currentTimeMillis() / 5000 * 5000;
        Assertions.assertEquals(10, dubboClient.getMethodCountPerCategory(0).get("timeoutError").get(timestamp));
        timestamp = timestamp / 15000 * 15000;
        Assertions.assertEquals(10, dubboMethod.getMethodCountPerCategory(0).get("timeoutError").get(timestamp));

    }

    @Test
    public void testProviderSuccess() throws Exception {
        IMetricManager metricManager = MetricManager.getIMetricManager();
        metricManager.clear();
        MetricsFilter metricsFilter = new MetricsFilter();
        Invocation invocation = new RpcInvocation("sayName", DemoService.class.getName(), "", new Class<?>[0], new Object[0]);
        RpcContext.getServiceContext().setRemoteAddress(NetUtils.getLocalHost(), 20880).setLocalAddress(NetUtils.getLocalHost(), 2345);
        URL url = getUrl().addParameter(SIDE_KEY, PROVIDER)
                .addParameter(TIMEOUT_KEY, 300);
        Invoker<DemoService> invoker = invokerFunction.apply(url);
        given(invoker.invoke(Mockito.any(Invocation.class))).willAnswer((invocation1)->AsyncRpcResult.newDefaultAsyncResult(1 ,(Invocation) invocation1.getArgument(0)));

        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> serviceInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(invoker, invoker, metricsFilter);

        for (int i = 0; i < 100; i++) {
            serviceInvokerNode.invoke(invocation);
        }
        FastCompass dubboClient = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_PROVIDER, MetricLevel.MAJOR));
        FastCompass dubboMethod = metricManager.getFastCompass(DUBBO_GROUP, new MetricName(DUBBO_PROVIDER_METHOD, new HashMap<String, String>(4) {
            {
                put(SERVICE, "org.apache.dubbo.monitor.dubbo.service.DemoService");
                put(METHOD, "void sayName()");
            }
        }, MetricLevel.NORMAL));
        long timestamp = System.currentTimeMillis() / 5000 * 5000;
        Assertions.assertEquals(100, dubboClient.getMethodCountPerCategory(0).get("success").get(timestamp));
        timestamp = timestamp / 15000 * 15000;
        Assertions.assertEquals(100, dubboMethod.getMethodCountPerCategory(0).get("success").get(timestamp));
    }

    @Test
    public void testInvokeMetricsService() {
        IMetricManager metricManager = MetricManager.getIMetricManager();
        metricManager.clear();
        MetricsFilter metricsFilter = new MetricsFilter();
        Invocation invocation = new RpcInvocation("sayName", DemoService.class.getName(), "", new Class<?>[0], new Object[0]);
        RpcContext.getServiceContext().setRemoteAddress(NetUtils.getLocalHost(), 20880).setLocalAddress(NetUtils.getLocalHost(), 2345);
        URL url = getUrl().addParameter(SIDE_KEY, PROVIDER)
                .addParameter(TIMEOUT_KEY, 300);
        Invoker<DemoService> serviceInvoker = invokerFunction.apply(url);
        Invoker<DemoService> timeoutInvoker = invokerFunction.apply(url);
        given(serviceInvoker.invoke(Mockito.any(Invocation.class))).willAnswer((invocation1)->AsyncRpcResult.newDefaultAsyncResult(1 ,(Invocation) invocation1.getArgument(0)));
        onInvokerThrows(timeoutInvoker);
        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> serviceInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(serviceInvoker, serviceInvoker, metricsFilter);
        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> timeoutInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(timeoutInvoker, timeoutInvoker, metricsFilter);

        for (int i = 0; i < 50; i++) {
            try {
                serviceInvokerNode.invoke(invocation);
                timeoutInvokerNode.invoke(invocation);
            } catch (RpcException e) {
                //ignore
            }
        }
        Protocol protocol = new DubboProtocol();
        url = URL.valueOf("dubbo://" + NetUtils.getLocalAddress().getHostName() + ":20880/" + MetricsService.class.getName());
        Invoker<MetricsService> invoker = protocol.refer(MetricsService.class, url);
        invocation = new RpcInvocation("getMetricsByGroup", DemoService.class.getName(), "", new Class<?>[]{String.class}, new Object[]{DUBBO_GROUP});
        try {
            Thread.sleep(5000);
        } catch (Exception e) {
            // ignore
        }
        String resStr = invoker.invoke(invocation).getValue().toString();
        List<MetricObject> metricObjectList = new Gson().fromJson(resStr, new TypeToken<List<MetricObject>>() {
        }.getType());
        Map<String, Object> metricMap = new HashMap<>();
        for (int i = 0; i < metricObjectList.size(); i++) {
            MetricObject object = metricObjectList.get(i);
            String metric = object.getMetric().substring(object.getMetric().lastIndexOf(".") + 1);
            if ((double) object.getValue() > 0.0 && object.getMetricLevel().equals(MetricLevel.MAJOR))
                metricMap.put(metric, object.getValue());
        }

        Assertions.assertEquals(50.0, metricMap.get("success_bucket_count"));
        Assertions.assertEquals(50.0, metricMap.get("timeoutError_bucket_count"));
        Assertions.assertEquals(100.0, metricMap.get("bucket_count"));
        Assertions.assertEquals(100.0 / 5, metricMap.get("qps"));
        Assertions.assertEquals(50.0 / 100.0, metricMap.get("success_rate"));
    }

    @Test
    public void testInvokeMetricsMethodService() {
        IMetricManager metricManager = MetricManager.getIMetricManager();
        metricManager.clear();
        MetricsFilter metricsFilter = new MetricsFilter();
        Invocation sayNameInvocation = new RpcInvocation("sayName", DemoService.class.getName(), "", new Class<?>[0], new Object[0]);
        Invocation echoInvocation = new RpcInvocation("echo", DemoService.class.getName(), "", new Class<?>[]{Integer.class}, new Integer[]{1});
        RpcContext.getServiceContext().setRemoteAddress(NetUtils.getLocalHost(), 20880).setLocalAddress(NetUtils.getLocalHost(), 2345);
        URL url = getUrl().addParameter(SIDE_KEY, PROVIDER)
                .addParameter(TIMEOUT_KEY, 300);
        Invoker<DemoService> serviceInvoker = invokerFunction.apply(url);
        Invoker<DemoService> timeoutInvoker = invokerFunction.apply(url);
        given(serviceInvoker.invoke(Mockito.any(Invocation.class))).willAnswer((invocation)->AsyncRpcResult.newDefaultAsyncResult(1 ,(Invocation) invocation.getArgument(0)));
        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> serviceInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(serviceInvoker, serviceInvoker, metricsFilter);
        FilterChainBuilder.LoopFilterChainNode<DemoService, Invoker<DemoService>, MetricsFilter> timeoutInvokerNode =
                new FilterChainBuilder.LoopFilterChainNode<>(timeoutInvoker, timeoutInvoker, metricsFilter);

        onInvokerThrows(timeoutInvoker);
        for (int i = 0; i < 50; i++) {
            serviceInvokerNode.invoke(sayNameInvocation);
            serviceInvokerNode.invoke(echoInvocation);
            try {
                timeoutInvokerNode.invoke(sayNameInvocation);
            } catch (RpcException e) {
                // ignore
            }
            try {
                timeoutInvokerNode.invoke(echoInvocation);
            } catch (RpcException e) {
                // ignore
            }
        }

        Protocol protocol = new DubboProtocol();
        url = URL.valueOf("dubbo://" + NetUtils.getLocalAddress().getHostName() + ":20880/" + MetricsService.class.getName());
        Invoker<MetricsService> invoker = protocol.refer(MetricsService.class, url);
        Invocation invocation = new RpcInvocation("getMetricsByGroup", DemoService.class.getName(), "", new Class<?>[]{String.class}, new Object[]{DUBBO_GROUP});
        try {
            Thread.sleep(15000);
        } catch (Exception e) {
            // ignore
        }
        String resStr = invoker.invoke(invocation).getValue().toString();
        List<MetricObject> metricObjectList = new Gson().fromJson(resStr, new TypeToken<List<MetricObject>>() {
        }.getType());
        Map<String, Map<String, Object>> methodMetricMap = new HashMap<>();
        for (int i = 0; i < metricObjectList.size(); i++) {
            MetricObject object = metricObjectList.get(i);
            String service = object.getTags().get("service");
            String method = service + "." + object.getTags().get("method");
            String metric = object.getMetric().substring(object.getMetric().lastIndexOf(".") + 1);
            Map map = methodMetricMap.get(method);
            if (map == null) {
                map = new HashMap();
                methodMetricMap.put(method, map);
            }
            map.put(metric, object.getValue());
        }

        Assertions.assertEquals(50.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void sayName()").get("success_bucket_count"));
        Assertions.assertEquals(50.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void echo(Integer)").get("success_bucket_count"));

        Assertions.assertEquals(50.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void sayName()").get("timeoutError_bucket_count"));
        Assertions.assertEquals(50.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void echo(Integer)").get("timeoutError_bucket_count"));

        Assertions.assertEquals(100.0 / 15,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void sayName()").get("qps"));
        Assertions.assertEquals(100.0 / 15,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void echo(Integer)").get("qps"));

        Assertions.assertEquals(50.0 / 100.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void sayName()").get("success_rate"));
        Assertions.assertEquals(50.0 / 100.0,
            methodMetricMap.get("org.apache.dubbo.monitor.dubbo.service.DemoService.void echo(Integer)").get("success_rate"));
    }
}
